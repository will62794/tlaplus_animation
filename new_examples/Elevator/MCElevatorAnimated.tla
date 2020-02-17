---- MODULE MCElevatorAnimated ----
EXTENDS TLC, ElevatorAnimated, FiniteSets

NotInit == ~Init
AllInElevator == ~(\A p \in Person : PersonState[p].location \in Elevator)

====