-------------------------------------------- MODULE Animation --------------------------------------------
EXTENDS Naturals, Sequences, Integers, TLC, FiniteSets

(**************************************************************************************************)
(* The Animation module provides functionality for creating an interactive visual animation of a  *)
(* TLA+ specification.  It allows you to visualize a particular execution trace by producing an   *)
(* SVG visualization for each "frame" i.e.  state of the trace.  This is done by defining a state *)
(* expression called a "View", which produces a set of graphical elements based on the variables  *)
(* of a specification.  For a specification with existing 'Init' and 'Next' predicates, an        *)
(* animation is defined as shown below:                                                           *)
(*                                                                                                *)
(* EXTENDS Animation                                                                              *)
(*                                                                                                *)
(* View == \* User-defined state expression                                                       *)
(*                                                                                                *)
(* AnimSpec ==                                                                                    *)
(*     /\ AnimatedInit(Init, View)                                                                *)
(*     /\ [][AnimatedNext(Next, View)]_<<vars, AnimationVars>>                                    *)
(*                                                                                                *)
(* where 'View' is a user defined state expression.  'vars' must be the tuple of all variables in *)
(* your existing spec.  The expressions AnimatedInit(Init, View) and AnimatedNext(Next, View)     *)
(* produce initial state and next state predicates that add auxiliary variables for tracking      *)
(* animation related state.  These variables should not affect the existing spec, as long as      *)
(* there are no name conflicts.  Adding these auxiliary variables may slow down model checking    *)
(* considerably.  Often, simulation mode seems to be more efficient for generating animated       *)
(* execution traces, since it does not incur the memory overhead of maintaining an explicit queue *)
(* of next states.  Hopefully this slowdown is acceptable, since the intended purpose of this     *)
(* Animation module is less about improving verification of TLA+ specs, and more about providing  *)
(* an alternative way to communicate TLA+ specs and associated models.                            *)
(*                                                                                                *)
(**************************************************************************************************)


(**************************************************************************************************)
(* Helper Operators                                                                               *)
(**************************************************************************************************)

\* Pick an arbitrary element of a given set
Pick(S) == CHOOSE x \in S : TRUE

\* Merge two records
Merge(r1, r2) == 
    LET D1 == DOMAIN r1 D2 == DOMAIN r2 IN
    [k \in (D1 \cup D2) |-> IF k \in D1 THEN r1[k] ELSE r2[k]]

\* The set of all permutations of elements of a set S whose length are the cardinality of S.
SeqPermutations(S) == LET Dom == 1..Cardinality(S) IN
                        {f \in [Dom -> S] : \A w \in S : \E v \in Dom : f[v]=w}

\* Convert a set to a sequence where the elements are in arbitrary order.
RECURSIVE SetToSeq(_)
SetToSeq(S) == IF S = {} THEN <<>> 
               ELSE LET v == Pick(S) IN <<v>> \o SetToSeq(S \ {v})

\* Join a sequence of strings with a specified delimiter.
RECURSIVE Join(_, _) 
Join(seq, delim) == 
    IF Len(seq) = 0 THEN ""
    ELSE IF Len(seq) = 1 THEN Head(seq) 
    ELSE (Head(seq) \o delim \o Join(Tail(seq), delim))

\* Quotify a given string.
Quote(s) == "'" \o s \o "'"

------------------------------------------

(**************************************************************************************************)
(*                                                                                                *)
(* Core Graphic Elements                                                                          *)
(*                                                                                                *)
(* Graphic primitives are represented using the same structure as SVG elements, but it is not     *)
(* necessary for users of this module to understand that internal detail.  These graphic          *)
(* primitives are what should be used to construct a 'View' expression.  Elements can be          *)
(* organized hierarchically using the 'Group' element.                                            *)
(*                                                                                                *)
(**************************************************************************************************)

\* A local, less verbose operator for converting a value to a string.
LOCAL _str(s) == ToString(s)


\* SVG element constructor.
LOCAL SVGElem(_name, _attrs, _children) == [name |-> _name, attrs |-> _attrs, children |-> _children ]

\* Construct an SVG View element.
LOCAL SVGView(w, h, children) == SVGElem("svg", [width |-> w, height |-> h], children)

\* Special element that SVGElemToString will interpret as a raw string.
LOCAL RawText(text) == SVGElem("_rawtext", [val |-> text], <<>>)

\* Convert an SVG element into its string representation.
RECURSIVE SVGElemToString(_)
SVGElemToString(elem) ==
    IF elem.name = "_rawtext" THEN elem.attrs.val ELSE
    LET childrenStr == Join([i \in DOMAIN elem.children |-> SVGElemToString(elem.children[i])], "") IN
    LET attrsStrSet == {Join(<<k, Quote(elem.attrs[k])>>, "=") : k \in DOMAIN elem.attrs} IN
    LET attrsStr == Join(SetToSeq(attrsStrSet), " ") IN
    Join(<<"<", elem.name, " ", attrsStr, ">", childrenStr , "</", elem.name,  ">">>, "")

\* All elements below can accept an 'attrs' argument. This is a function mapping string
\* keys to string values. These key-value pairs describe any additional SVG attributes of the element. To pass 
\* no attributes, just pass attrs=<<>>.

\* Line element. 'x1', 'y1', 'x2', and 'y2' should be given as integers.
Line(x1, y1, x2, y2, attrs) == 
    LET svgAttrs == [x1 |-> _str(x1), 
                     y1 |-> _str(y1), 
                     x2 |-> _str(x2),
                     y2 |-> _str(y2)] IN
    SVGElem("line", Merge(svgAttrs, attrs), <<>>)

\* Circle element. 'cx', 'cy', and 'r' should be given as integers.
Circle(cx, cy, r, attrs) == 
    LET svgAttrs == [cx |-> _str(cx), 
                     cy |-> _str(cy), 
                     r  |-> _str(r)] IN
    SVGElem("circle", Merge(svgAttrs, attrs), <<>>)

\* Rectangle element. 'x', 'y', 'w', and 'h' should be given as integers.
Rect(x, y, w, h, attrs) == 
    LET svgAttrs == [x      |-> _str(x), 
                     y      |-> _str(y), 
                     width  |-> _str(w), 
                     height |-> _str(h)] IN
    SVGElem("rect", Merge(svgAttrs, attrs), <<>>)

\* Text element.'x', and 'y' should be given as integers, and 'text' given as a string.
Text(x, y, text, attrs) == 
    LET svgAttrs == [x |-> _str(x), 
                     y |-> _str(y)] IN
    SVGElem("text", Merge(svgAttrs, attrs), <<RawText(text)>>) 

\* Group element. 'children' is as a sequence of elements that will be contained in this group.
Group(children, attrs) == SVGElem("g", attrs, children)

------------------------------------------

(**************************************************************************************************)
(*                                                                                                *)
(* Animation Operators and Variables                                                              *)
(*                                                                                                *)
(* The variables below are used to construct a sequence of animation frames.  Upon each step of   *)
(* an execution trace, we construct a new frame and convert it to an SVG string, and append it to *)
(* the global 'svgAnimationString' variable.  When the trace completes, this string should be     *)
(* suitable to copy into an HTML template that displays an animation frame sequence.              *)
(*                                                                                                *)
(**************************************************************************************************)

\* The global SVG string that stores the sequence of all animation frames.
VARIABLE svgAnimationString

\* Index representing what frame number we are currently on.
VARIABLE frameInd

\* The name of the current action being executed. (Optional)
VARIABLE actionName

AnimationVars == <<svgAnimationString, frameInd, actionName>>

LOCAL ActionNameElem(name) == Text(10, 30, "Next Action: " \o name, <<>>)

\* Builds a single frame 'i' for part of a sequence of animation frames. This is an SVG group element that 
\* contains identifying information about the frame.
LOCAL MakeFrame(elem, action, i) == 
    LET attrs == [class |-> "frame", id |-> ToString(i), action |-> action] IN
    Group(<<elem, ActionNameElem(action)>>, attrs)
    
ActionName(str) == actionName' = str   

\* Produces an initial state predicate for animation.                                             *)
AnimatedInit(Init, View) ==
    /\ Init
    /\ frameInd = 0
    /\ actionName = ""
    /\ svgAnimationString = SVGElemToString(MakeFrame(View, "Init", 0))

\*
\* Produces a next-state relation for animation.
\*
\* 'View' is a state expression that produces a graphic element visualizing the state of a spec's
\* variables.  'Next' is the next state relation of the original spec.
\*
AnimatedNext(Next, View, UseActionNames) == 
    /\ Next
    /\ frameInd' = frameInd + 1
    /\ IF UseActionNames THEN TRUE ELSE UNCHANGED actionName
    \* For efficiency, we don't explicitly keep a running sequence of all animation
    \* frames. When an action occurs, we simply generate the current frame, convert it
    \* to its SVG string representation, and append the string to the existing, global
    \* SVG animation string. This way we don't have to regenerate the SVG strings
    \* for past frames every time a new action occurs.
    /\ LET frame == MakeFrame(View, actionName', frameInd') IN 
           svgAnimationString' = svgAnimationString \o SVGElemToString(frame)

    
====================================================================================================
\* Modification History
\* Last modified Sun Jul 08 21:00:11 EDT 2018 by williamschultz
\* Created Thu Mar 22 23:59:48 EDT 2018 by williamschultz
