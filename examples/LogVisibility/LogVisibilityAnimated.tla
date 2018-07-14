---------------------------------- MODULE LogVisibilityAnimated ----------------------------------
EXTENDS Integers, Animation, LogVisibility

States == {"Available", "Pending", "Committed", "Aborted"}

StateColor(state) == 
    CASE state = "Available" -> "lightgray"
      [] state = "Pending"   -> "yellow"
      [] state = "Committed" -> "green"
      [] state = "Aborted"   -> "red"
      [] OTHER -> "gray"

SlotDims == [w |-> 90, h |-> 90]
SlotColor(i) == StateColor(slots[i].state)
        
SlotRect(i) == 
    LET label == Text(i * (SlotDims.w + 5) + 20, 20, ToString(i), [font |-> "Arial"])
        rect == Rect(i * (SlotDims.w + 5), 30, SlotDims.w, SlotDims.h, [fill |-> SlotColor(i)]) IN
        Group(<<label, rect>>, <<>>)

SlotRects == {SlotRect(i) : i \in DOMAIN slots}

SlotNumber(i) == Text((maxVisibleSlot + 1) * (SlotDims.w + 5), 130, "Visibility Point", [font |-> "Arial"])

VisibilityPoint == Rect((maxVisibleSlot + 1) * (SlotDims.w + 5), 145, 3, 20, [fill |-> "orange"])
VisibilityText == Text((maxVisibleSlot + 1) * (SlotDims.w + 5), 180, "Visibility Point=" \o ToString(maxVisibleSlot), [font |-> "Arial"])

LegendState(k, state) == 
    LET rect == Rect(5, k*30, 20, 20, [fill |-> StateColor(state)])
        label == Text(35, (k*30 + 15), state, [font |-> "Arial"]) IN
        Group(<<rect, label>>, ("transform" :> "translate(800 190)"))
        
Legend == LET StateSeq == SetToSeq(States) IN
              {LegendState(i, StateSeq[i]) : i \in DOMAIN StateSeq}
    
Elems == SlotRects \cup {VisibilityPoint, VisibilityText} \cup Legend

View == Group(SetToSeq(Elems), ("transform" :> "translate(80 50)"))

vars == <<clock, slots, maxVisibleSlot>>

AnnotatedNext == 
    \/ StartTxn                             /\ ActionName("StartTxn("  \o ToString(clock) \o ")")
    \/ \E i \in DOMAIN slots : CommitTxn(i) /\ ActionName("CommitTxn(" \o ToString(i) \o ")")
    \/ \E i \in DOMAIN slots : AbortTxn(i)  /\ ActionName("AbortTxn("  \o ToString(i) \o ")")

AnimSpec ==
    /\ AnimatedInit(Init, View)
    /\ [][AnimatedNext(AnnotatedNext, View, TRUE)]_<<vars, AnimationVars>>
    
----

\* Helpful definitions for model.

MaxClock==6

\* Can override the definition of 'Nat' with 'ModelNat'
ModelNat == 0..MaxClock

\* State constraint to make state space finite.
StateConstraint == clock <= MaxClock


====================================================================================================
\* Modification History
\* Last modified Sat Jul 14 15:31:43 EDT 2018 by williamschultz
\* Created Wed May 09 20:38:43 EDT 2018 by williamschultz
