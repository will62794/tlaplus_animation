--------------------------------------- MODULE RaftAnimated ---------------------------------------

EXTENDS Animation, Integers, RaftSimpler

(*** Generic Helpers ***)

Injective(f) == \A x, y \in DOMAIN f : f[x] = f[y] => x = y

\* Linearly interpolate a position halfway between two given points. 't', the interpolation factor, is measured
\* on a scale from 0 to 100.
Interp(p1, p2, t) ==
    [ x |-> (t * p1.x + (100-t) * p2.x) \div 100 , 
      y |-> (t * p1.y + (100-t) * p2.y) \div 100]
  
\* Translate a point by a specified amount.
Move(p, dx, dy) == [x |-> p.x + dx, y |-> p.y + dy]  

\* Reverse a sequence.
Reverse(s) == [ i \in DOMAIN s |-> s[Len(s)-i+1]]

(*** Server Elements ***)

\* Establish a fixed mapping to assign an ordering to elements in these sets.
ServerId == CHOOSE f \in [Server -> 1..Cardinality(Server)] : Injective(f)

\* This animation assumes 3 servers.
Base == [x |-> 450, y |-> 100]
ServerPositions == 
      1 :> [x |-> Base.x, y |-> Base.y] @@ 
      2 :> [x |-> Base.x - 200, y |-> Base.y + 300] @@
      3 :> [x |-> Base.x + 200, y |-> Base.y + 300]

\* Colors to represent the state of a server. 
StateColor ==
      Leader :> "green" @@ 
      Candidate :> "yellow" @@
      Follower :> "darkgray"

\* Generates a graphic element representing server 'sid'.
ServerElem(sid) == 
    LET pos == ServerPositions[ServerId[sid]]
        circleAttrs == ("stroke" :> "black" @@ "stroke-width" :> "1" @@ "fill" :> StateColor[state[sid]])
        circle == Circle(pos.x, pos.y, 27, circleAttrs)
        termLabel == Text(pos.x, pos.y + 45, ToString(currentTerm[sid]), [fill |-> "red"])
        serverLabel == Text(pos.x - 7, pos.y - 35, "n" \o ToString(sid), [fill |-> "black"]) IN
        Group(<<serverLabel, termLabel, circle>>, <<>>)
               
VotesGranted(s) == 
    LET pos == ServerPositions[ServerId[s]] IN
    Text(pos.x - 15, pos.y + 75, "votes: " \o ToString(votesGranted[s]), ("font-size" :> "11"))

ServerElems == {Group(<<ServerElem(s), VotesGranted(s)>>, <<>>) : s \in Server}

(*** Message Elements ***)

\* Constructs a message element at position 'pos'.
MessageElem(m, pos) == 
    LET text ==
    CASE m.mtype = RequestVoteRequest -> 
                    "VoteRequest" \o " (" \o 
                    Join( << Join(<<"term", ToString(m.mterm)>>, "="), 
                             Join(<<"from", ToString(m.msource)>>, "=") >>, ", ") \o ")"
       [] m.mtype = RequestVoteResponse -> 
                    "VoteResponse" \o " (" \o 
                    Join( << Join(<<"term", ToString(m.mterm)>>, "="), 
                             Join(<<"from", ToString(m.msource)>>, "="),
                             Join(<<"granted", ToString(m.mvoteGranted)>>, "=")  >>, ", ") \o ")"             
       [] m.mtype = AppendEntriesRequest -> 
                    "AppendEntries" \o " (" \o 
                    Join( << Join(<<"term", ToString(m.mterm)>>, "="), 
                             ToString(m.mentries) >>, ", ") \o ")" 
    [] OTHER -> ToString(m.mtype) IN
    Text(pos.x, pos.y, text,  ("font-size" :> "12"))

\* Produces a group of graphic elements for a given set of messages.
MessageList(msgs, basePos) == 
    IF msgs = {} THEN Group(<<>>, <<>>) ELSE
    LET msgList == Reverse(SetToSeq(msgs))
        msgElems == {MessageElem(msgList[i], [x |-> basePos.x, y |-> basePos.y + (i*15)]) : i \in DOMAIN msgList} IN
        Group(SetToSeq(msgElems), <<>>)

\* The set of all messages in flight to a particular server.
IncomingMessages(sid) == {m \in DOMAIN messages : m.mdest = sid /\ messages[m] > 0}

MessageElems == {MessageList(IncomingMessages(s), Move(ServerPositions[ServerId[s]], 35, 10)) : s \in Server}

\* The position of a log slot for a server and log index.
LogEntryDims == [w |-> 30, h |-> 30]
LogPos(s, i) == [x |-> 780 + i * (LogEntryDims.w + 3) , y |-> 100 + ServerId[s] * (LogEntryDims.h + 3)]

\* Generate a single log entry element at index 'i' for server 'sid'.
LogEntryElem(sid, i) == 
    LET pos == LogPos(sid, i) 
        entry == Rect(pos.x, pos.y, LogEntryDims.w, LogEntryDims.h, [fill |-> "lightblue"])
        term == Text((pos.x + LogEntryDims.w \div 2 - 6), (pos.y + LogEntryDims.h \div 2 + 8), ToString(log[sid][i].term),  ("font-size" :> "18")) IN
    Group(<<entry, term>>, <<>>)
    
LogElem(sid) == 
    LET entryElems == {LogEntryElem(sid, i) : i \in DOMAIN log[sid]} IN
    Group(SetToSeq(entryElems), <<>>)
    
LogElems == {LogElem(s) : s \in Server}

(*** Log Slot Elements ***)
MaxLogSlots == 5
LogSlot(sid, i) == Rect(LogPos(sid, i).x, LogPos(sid, i).y, LogEntryDims.w, LogEntryDims.h, ("stroke" :> "black" @@ "stroke-width" :> "1" @@ "fill" :> "white"))
LogSlotElem(sid) == 
    LET slotElems == {LogSlot(sid, i) : i \in 1..MaxLogSlots} IN
    Group(SetToSeq(slotElems), <<>>)
LogSlotElems == {LogSlotElem(s) : s \in Server}

LogLabel(s) == Text((LogPos(s, 0).x-12), (LogPos(s, 0).y + 16), ToString(s), ("font-size" :> "16"))
LogLabels == {LogLabel(s) : s \in Server}

\* All graphic elements.
AllElems == SetToSeq(ServerElems) \o 
            SetToSeq(MessageElems) \o 
            SetToSeq(LogSlotElems) \o
            SetToSeq(LogElems) \o
            SetToSeq(LogLabels) 
            

View == Group(AllElems, <<>>)  

AnimatedSpec == \* Initialize state with Init and transition with Next, subject to TemporalAssumptions
    /\ AnimatedInit(Init, View)
    /\ [][AnimatedNext(Next, View, FALSE)]_<<vars,AnimationVars>> 
    
(****************************************************)
(* A pre-defined trace that we want to animate.     *)
(****************************************************)

TraceInit == Init

TraceNext == 
    /\ allLogs' = allLogs \cup {log[i] : i \in Server} 
    /\ \* Let node 0 become leader in term 2.
       \/ Timeout(0) /\ currentTerm[0] = 1
       \/ \E j \in Server : RequestVote(0, j) /\ currentTerm[0] = 1
       \/ BecomeLeader(0)
       \/ ClientRequest(0, "v1") /\ currentTerm[0] = 2
       
       \* Let node 2 become leader in term 3.
       \/ Timeout(2) /\ currentTerm[2] = 2 /\ currentTerm[0] = 2 /\ state[0] = Leader /\ Len(log[0]) > 0
       \/ RequestVote(2, 1) /\ currentTerm[2] = 3 
       \/ RequestVote(2, 2) /\ currentTerm[2] = 3
       \/ BecomeLeader(2)
       \/ ClientRequest(2, "v1") /\ currentTerm[2] = 3 
       \/ AppendEntries(2, 1) /\ currentTerm[0] = 3
       
       \* Let node 0 become leader again in term 4.
       \/ Timeout(0) /\ currentTerm[0] = 3 /\ currentTerm[2] = 3 /\ state[2] = Leader /\ Len(log[2]) > 0
       \/ \E j \in Server : RequestVote(0, j)
       \/ BecomeLeader(0)
       \/ ClientRequest(0, "v1") /\ currentTerm[0] = 4
       \/ AppendEntries(0, 1) /\ currentTerm[0] = 4

       \* Node2 becomes leader once again, in term 5.
       \/ Restart(0) /\ currentTerm[0] = 4 /\ state[0] = Leader /\ Len(log[1]) > 0 
       \/ Timeout(2) /\ currentTerm[0] = 4 /\ state[0] = Leader /\ Len(log[1]) > 0
       \/ RequestVote(2, 1) /\ currentTerm[2] = 5
       \/ RequestVote(2, 2) /\ currentTerm[2] = 5
       \/ BecomeLeader(2) /\ currentTerm[2] = 5
       
       \* New leader replicates an entry that overwrites the first log entry on node 1.
       \/ AppendEntries(2, 1) /\ currentTerm[2] = 5
       \/ ClientRequest(2, "v1") /\ currentTerm[2] = 5
       \/ AdvanceCommitIndex(2) /\ currentTerm[2] = 5
       
       \/ \E m \in DOMAIN messages : 
            /\ messages[m] > 0  \* Message must actually be in transit.
            /\ Receive(m)

TraceAnimatedSpec == \* Initialize state with Init and transition with Next, subject to TemporalAssumptions
    /\ AnimatedInit(TraceInit, View)
    /\ [][AnimatedNext(TraceNext, View, FALSE)]_<<vars,AnimationVars>>    

====================================================================================================
\* Modification History
\* Last modified Sun Jul 08 12:24:21 EDT 2018 by williamschultz
\* Created Sun Mar 25 12:40:58 EDT 2018 by williamschultz
