# TLA+ Animation Module

This is a TLA+ module for creating visualizations of TLC execution traces that can be run inside a web browser. To create an animation, you can start with an existing TLA+ specification and define a "view" expression, which is a TLA+ state expression that produces a set of graphical elements based on the values of the variables declared in your specification. The Animation module, when used in conjunction with TLC, constructs a sequence of frames, where each frame is the value of the view expression at a step in an execution trace. The module uses SVG elements as its graphical primitives, which allows for flexibility and variety in the visualizations that can be produced. 

## How To Use

If you have an existing specification with initial state and next state predicates `Init` and `Next`, and with variables `vars`, you can define an animated version of this spec by defining the following expression:

```tla
AnimatedSpec ==
    /\ AnimatedInit(Init, View)
    /\ [][AnimatedNext(Next, View, FALSE)]_<<vars,AnimationVars>>  
```

where `View` is your defined view state expression. To produce the animation, you can set `AnimatedSpec` as the specification for TLC to check, and set up some way for TLC to produce a specific error trace. For example, you could define an invariant whose violation produces an interesting execution you would like to visualize. Or, you could just run TLC in simulation mode to see what some random execution looks like when visualized. When the error trace is produced, the state of the `svgAnimationString` variable for the final state will be a string containing a sequence of SVG elements where each is a frame of that trace. You can copy and paste this string into an HTML template and view the animation in a browser.

If you are using the TLA+ Toolbox, a convenient way to define an animation for an existing spec called `Spec.tla` is to create a new spec called `SpecAnimated.tla`. Inside `SpecAnimated.tla` you can define your view expression and any related animation operators, and define the animated version of your spec (`AnimatedSpec` as shown in the example snippet above). In order to have access to the operators and variables of your original module, and also to those of the `Animation` module you can add the directory of `Spec.tla` and `Animation.tla` to the TLA+ library path locations. You can edit these by clicking on the name of a spec in the toolbox and selecting `Properties`. Doing this will then allow you to automatically include your original module and the `Animation` module, without explicitly copying them to your new animated spec's directory. Also, any changes you make to your original spec will automatically be reflected in the version included in your animated spec.

