---- MODULE MCElevatorAnimated ----
EXTENDS TLC, ElevatorAnimated, FiniteSets

NotInit == ~Init
NoElevatorCalls == Cardinality(ActiveElevatorCalls) < 2

====