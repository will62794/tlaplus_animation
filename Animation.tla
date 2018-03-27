-------------------------------------------- MODULE Animation --------------------------------------------
EXTENDS Naturals, Sequences, TLC, FiniteSets

(*
    This module provides definitions for creating an interactive visual animation of a 
    TLA+ specification. It allows you to visualize a particular trace by producing an
    SVG visualization for each "frame" i.e. state of the trace. A user of this module
    simply has to provide their own "View" function which is an expression
    that should depend on any variables of their spec and produces a singe visual element 
    (defined below).
*)

(*** Generic Helpers ***)

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

(*** Core Graphic Elements 
    
    Internally we represent elements as SVG elements, but it is not necessary for
    users of this module to understand that internal detail. ***)

\* Core SVG element constructor.
LOCAL SVGElem(_name, _attrs, _children) == [name |-> _name, attrs |-> _attrs, children |-> _children ]

\* Construct an SVG View element.
LOCAL SVGView(w, h, children) == SVGElem("svg", [width |-> w, height |-> h], children)

\* Convert an SVG element into its string representation.
RECURSIVE SVGElemToString(_)
SVGElemToString(elem) ==
    IF elem.name = "_rawtext" THEN elem.attrs.val ELSE
    LET childrenStr == Join([i \in DOMAIN elem.children |-> SVGElemToString(elem.children[i])], "") IN
    LET attrsStrSet == {Join(<<k, Quote(elem.attrs[k])>>, "=") : k \in DOMAIN elem.attrs} IN
    LET attrsStr == Join(SetToSeq(attrsStrSet), " ") IN
    Join(<<"<", elem.name, " ", attrsStr, ">", childrenStr , "</", elem.name,  ">">>, "")

(* Core graphic element and container constructors. *)
Circle(cx, cy, r, attrs) == SVGElem("circle", Merge([cx |-> cx, cy |-> cy, r |-> r], attrs), <<>>)
Rect(x, y, w, h, attrs) == SVGElem("rect", Merge([x |-> x, y |-> y, width |-> w, height |-> h], attrs), <<>>)

RawText(text) == SVGElem("_rawtext", [val |-> text], <<>>)
Text(x, y, text, attrs) == SVGElem("text", Merge([x |-> x, y |-> y], attrs), <<RawText(text)>>) 

Group(children, attrs) == SVGElem("g", attrs, children)

------------------------------------------

(*** Animation Operators ***)

\* The two variables below are used to save the frame history explicitly, so when model checking finishes, we
\* have all frames for the animation. 'animationFrames' is a sequence of animation states, where each
\* entry is a graphic element representing single state in a trace. 'svgAnimationString' is
\* the raw SVG string representation of the current 'animationFrames' sequence. 
\*VARIABLE animationFrames
VARIABLE svgAnimationString
VARIABLE frameInd

AnimationVars == <<svgAnimationString, frameInd>>

MakeFrame(elem, i) == Group(<<elem>>, [class |-> "frame", id |-> ToString(i)])
    
\*SVGStr == SVGElemToString(SVGView("500", "500", animationFrames))

AnimatedInit(Init, View) ==
    /\ Init
    /\ frameInd = 0
    /\ svgAnimationString = SVGElemToString(MakeFrame(View, 0))

AnimatedNext(Next, View) == 
    /\ Next
    /\ frameInd' = frameInd + 1
    \* For efficiency, we don't explicitly keep a running sequence of all animation
    \* frames. When an action occurs, we simply generate the current frame, convert it
    \* to its SVG string representation, and append the string to the existing, global
    \* SVG animation string. This way we don't have to regenerate the SVG strings
    \* for past frames every time a new action occurs.
    /\ LET frame == MakeFrame(View, frameInd) IN 
       svgAnimationString' = svgAnimationString \o SVGElemToString(frame)
    
====================================================================================================
\* Modification History
\* Last modified Mon Mar 26 23:39:10 EDT 2018 by williamschultz
\* Created Thu Mar 22 23:59:48 EDT 2018 by williamschultz
