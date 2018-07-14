------------------------------------- MODULE LogVisibility -------------------------------------
EXTENDS Integers, TLC

\*
\* A very simple model illustrating the concept of transaction log visibility. The "log" in this model is a sequence
\* of operations (transactions), but each 'slot' of the log may be written to concurrently. Concurrent transactions are
\* assigned timestamps (slots ids in this model), which defines their slot position. Since timestamp order
\* does not necessarily reflect real time commit order, there must be some mechanism for ensuring that reads up
\* to a certain position in the log do not return sections of the log with "holes". To do this, we enforce 
\* a log "visibility" rule, which says that you are not allowed to read up to a certain slot of the log unitl
\* it is known that the state of all previous slots are "set in stone" i.e. they will never change. 
\* These concepts are expressed more precisely below.
\*

\* A monotonically increasing integral counter.
VARIABLE clock

\* A function mapping slot ids to "slots". Each slot represents a position
\* in the log that can either be "filled" by an operation, or left empty.
\* Every slot is uniquely identified by its id. In a real system, these slot ids 
\* could likely be timestamps.
VARIABLE slots

\* For demonstration, we include the "visibility" point as an explicit variable in the model. This is maximum 
\* slot at which it is valid to read from.
VARIABLE maxVisibleSlot

Maximum(S) == CHOOSE x \in S : \A y \in S : x >= y

\* Expression determining whether a particular slot 's' should be considered "visible". This means
\* that it is valid to read at this slot position. All slots earlier than it must have either
\* committed or aborted.
Visible(i) == 
    /\ i \in DOMAIN slots
    /\ \A s \in DOMAIN slots : s <= i => slots[s].state \in {"Committed", "Aborted"}

MaxVisibleSlot == 
    LET visibleSlots == {i \in DOMAIN slots : Visible(i)} IN
    IF visibleSlots = {} THEN -1 ELSE Maximum(visibleSlots)

StartTxn == 
    /\ clock' = clock + 1
    /\ slots' = [slots EXCEPT ![clock] = [state |-> "Pending"]]
    /\ maxVisibleSlot' = MaxVisibleSlot'
   
CommitTxn(i) == 
    /\ slots[i].state = "Pending"
    /\ slots' = [slots EXCEPT ![i] = [state |-> "Committed"]]
    /\ maxVisibleSlot' = MaxVisibleSlot'
    /\ UNCHANGED clock
    
AbortTxn(i) == 
    /\ slots[i].state = "Pending"
    /\ slots' = [slots EXCEPT ![i] = [state |-> "Aborted"]] 
    /\ maxVisibleSlot' = MaxVisibleSlot'
    /\ UNCHANGED clock

Init == 
    /\ clock = 0
    \* All slots are initially unused. If a slot id doesn't exist in the domain of 'slots',
    \* it means that that slot is available.
    /\ slots = [n \in Nat |-> [state |-> "Available"]]
    /\ maxVisibleSlot = -1

Next == 
    \/ StartTxn
    \/ \E i \in DOMAIN slots : CommitTxn(i)
    \/ \E i \in DOMAIN slots : AbortTxn(i)

====================================================================================================
\* Modification History
\* Last modified Wed May 09 21:06:34 EDT 2018 by williamschultz
\* Created Wed May 09 19:47:13 EDT 2018 by williamschultz
