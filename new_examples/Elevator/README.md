## Elevator TLA+ Animation

To generate a trace with TLC and produce an animation for the `Elevator.tla` spec in this directory, run the following commands:

```
# Download latest TLC tools JAR.
./get_tlatools.sh

# Model checks the spec under simulation mode and produces an error trace.
./model_check.sh MCElevatorAnimated

# Runs trace exploration to generate animated trace and generates HTML output.
./trace_explore.sh MCElevatorAnimated
```

The visualization itself is defined in `ElevatorAnimated.tla`. You can go in there and tweak the layout of the visualization and re-run trace exploration step to produce a new animation HTML. Once you have run model checking once, the TLC output will be saved in the `MCElevatorAnimated.out` file, which is the input fed into the trace explorer. So, once you run model checking and produce an output file, you can continue producing animations of that trace without re-running the model checker. If you want to animate a different trace, then you will need to run the model checker again followed by trace explorer. 
