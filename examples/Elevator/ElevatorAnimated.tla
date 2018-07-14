------------------------------------- MODULE ElevatorAnimated -------------------------------------

(**************************************************************************************************)
(* Animation and View Definitions for Elevator system                                             *)
(**************************************************************************************************)

EXTENDS Elevator, Animation


(* View helpers. *)
Injective(f) == \A x, y \in DOMAIN f : f[x] = f[y] => x = y

\* Establish a fixed mapping to assign an ordering to elements in these sets.
PersonId == CHOOSE f \in [Person -> 1..Cardinality(Person)] : Injective(f)
ElevatorId == CHOOSE f \in [Elevator -> 1..Cardinality(Elevator)] : Injective(f)

\* Dimensions of an elevator.
ElevatorDims == [width |-> 35, height |-> 50]
FloorHeight == ElevatorDims.height + 10
FloorYPos(f) == f * FloorHeight

\* Gives the (x,y) base position of an elevator.
ElevatorPos(e) ==  [x |-> (150 + ElevatorId[e] * (ElevatorDims.width + 3)), y |-> FloorYPos(ElevatorState[e].floor)]
    
(**************************************************************************************************)
(* ELEVATOR elements.                                                                             *)
(**************************************************************************************************)
ElevatorElem(e) ==  
    LET pos == ElevatorPos(e)
        dims == ElevatorDims 
        color == IF ElevatorState[e].doorsOpen THEN "green" ELSE "black" IN
    Rect(ToString(pos.x), ToString(pos.y), ToString(dims.width), ToString(dims.height), [fill |-> color])   

\* Elements that show which direction an elevator is moving.
ElevatorDirElem(e) == 
    LET pos == ElevatorPos(e)
        dims == ElevatorDims 
        mid == pos.y + 17
        yPos == IF ElevatorState[e].direction = "Down" 
                    THEN mid - 17
                    ELSE IF ElevatorState[e].direction = "Up" THEN mid + 17
                    ELSE mid IN
    Rect(ToString(pos.x + 1), ToString(yPos), ToString(dims.width-2), "2", [fill |-> "white"])     

ElevatorDirElems == {ElevatorDirElem(e) : e \in Elevator}
ElevatorElems == {ElevatorElem(e) : e \in Elevator}

(**************************************************************************************************)
(* PERSON Elements.                                                                               *)
(**************************************************************************************************) 

PersonRadius == 3
PersonXPosBase == 30
PersonXPos(xBase, p) == xBase + (p * 9)
PersonYPos(p) == FloorYPos(PersonState[p].location) + 10

\* Person who is currently on a floor, not in an elevator.
FloorPersonElem(p) == 
    LET person == PersonState[p]
        pos == [y |-> PersonYPos(p), x |-> PersonXPos(PersonXPosBase, p)]
        color == IF person.waiting THEN "darkred" ELSE "blue" IN
        Circle(ToString(pos.x), ToString(pos.y), ToString(PersonRadius), [fill |-> color])

\* Person who is currently in an elevator.
ElevatorPersonElem(p) == 
    LET person == PersonState[p]
        elevPos == ElevatorPos(person.location) 
        pos == [elevPos EXCEPT !.x = PersonXPos(elevPos.x, p), !.y = @ + 10] IN
        Circle(ToString(pos.x), ToString(pos.y), ToString(PersonRadius), [fill |-> "gray"])   

PersonElem(p) == 
    \* A person should always be waiting or in an elevator.
    LET person == PersonState[p] IN
    CASE person.location \in Floor -> FloorPersonElem(p)
      [] person.location \in Elevator -> ElevatorPersonElem(p)
      
PersonDestinationElem(p) ==
    LET person == PersonState[p] IN
    CASE person.location \in Floor -> 
            LET xPos == PersonXPos(PersonXPosBase, p) 
                dims == (IF (person.destination > person.location)
                    THEN [height |-> (FloorYPos(person.destination) - PersonYPos(p)),
                          yPos   |-> PersonYPos(p)]
                    ELSE [height |->  (PersonYPos(p) - FloorYPos(person.destination)),
                          yPos   |->  FloorYPos(person.destination)]) IN
                Rect(ToString(xPos), ToString(dims.yPos), "1", ToString(dims.height), [fill |-> "lightgray"])
      [] person.location \in Elevator -> 
            LET elevator == ElevatorState[person.location]
                elevPos == ElevatorPos(person.location) 
                xPos == PersonXPos(elevPos.x, p) 
                personYPos == elevPos.y + 10
                dims == (IF (person.destination > elevator.floor)
                    THEN [height |-> (FloorYPos(person.destination) - personYPos),
                          yPos   |-> personYPos]
                    ELSE [height |->  (personYPos - FloorYPos(person.destination)),
                          yPos   |->  FloorYPos(person.destination)]) IN
                Rect(ToString(xPos), ToString(dims.yPos), "1", ToString(dims.height), [fill |-> "lightgray"])
          
PersonDestinationElems == {PersonDestinationElem(p) : p \in Person}
PeopleTitle == Text(ToString(PersonXPosBase), "30", "People", <<>>)
PersonElems == {PersonElem(p) : p \in Person} \cup PersonDestinationElems

(**************************************************************************************************)
(* ELEVATOR CALL elements.                                                                        *)
(**************************************************************************************************)
IsFloorCall(floor, dir) == \E c \in ActiveElevatorCalls : c.floor = floor /\ c.direction = dir

ButtonXPos == 90
Button(floor, dir) == 
    LET x == ButtonXPos
        y == FloorYPos(floor) + (IF dir = "Up" THEN 25 ELSE 16) IN
        Rect(ToString(x), ToString(y), "7", "7", [fill |-> IF IsFloorCall(floor, dir) THEN "orange" ELSE "black"])

ElevatorButtonElem(floor) ==
    LET upButton == Button(floor, "Up")
        downButton ==  Button(floor, "Down") IN
        Group(<<upButton, downButton>>, <<>>)

ElevatorButtonElems == {ElevatorButtonElem(f) : f \in Floor}

(**************************************************************************************************)
(* FLOOR elements.                                                                                *)
(**************************************************************************************************)

FloorSeparator(floor) == Rect(ToString(5), ToString(FloorYPos(floor)), "350", "1", [fill |-> "lightgray"])
FloorSeparators == {FloorSeparator(f) : f \in Floor}

FloorLabel(floor) == Text("10", ToString(FloorYPos(floor)+15), ToString(floor), <<>>)
FloorLabels == {FloorLabel(f) : f \in Floor}

FloorElems == UNION {FloorLabels, FloorSeparators}

AllElems == SetToSeq(ElevatorElems) \o SetToSeq(UNION {FloorElems, ElevatorDirElems, ElevatorButtonElems, PersonElems})

View == Group(AllElems, ("transform" :> "translate(400 30)"))

----------------------------------------------------------------- 
Maximum(S) == CHOOSE x \in S : \A y \in S : x >= y

ReducedInit == 
    \* Have people start at a random even floor. Reduce the number of initial states by limiting initial destinations.
    /\ PersonState \in [Person -> [location : {x \in Floor : x % 2 = 0 }, 
                                   destination : {1, Maximum(Floor)}, 
                                   waiting : {FALSE}]]
    /\ ActiveElevatorCalls = {}
    \* Have all elevators start at the first floor.
    /\ ElevatorState \in [Elevator -> [floor : {1}, direction : {"Stationary"}, doorsOpen : {FALSE}, buttonsPressed : {{}}]]

AnnotatedNext == \* The animation next-state relation.
    \/ \E p \in Person : PickNewDestination(p)      /\ ActionName("PickNewDestination")
    \/ \E p \in Person : CallElevator(p)            /\ ActionName("CallNewElevator")
    \/ \E e \in Elevator : OpenElevatorDoors(e)     /\ ActionName("OpenElevatorDoors")
    \/ \E e \in Elevator : EnterElevator(e)         /\ ActionName("EnterElevator")
    \/ \E e \in Elevator : ExitElevator(e)          /\ ActionName("ExitElevator")
    \/ \E e \in Elevator : CloseElevatorDoors(e)    /\ ActionName("CloseElevatorDoors")
    \/ \E e \in Elevator : MoveElevator(e)          /\ ActionName("MoveElevator")
    \/ \E e \in Elevator : StopElevator(e)          /\ ActionName("StopElevator")
    \/ \E c \in ElevatorCall : DispatchElevator(c)  /\ ActionName("DispatchElevator")

AnimSpec ==
    /\ AnimatedInit(ReducedInit, View)
    /\ [][AnimatedNext(AnnotatedNext, View, TRUE)]_<<Vars,AnimationVars>>

====================================================================================================
\* Modification History
\* Last modified Sat Jul 07 16:26:03 EDT 2018 by williamschultz
\* Created Fri Mar 23 00:50:27 EDT 2018 by williamschultz
