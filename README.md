# TLA+ Animation Module

This is a TLA+ module for creating visualizations of TLC execution traces that can be run inside a web browser. To create an animation, you can start with an existing TLA+ specification and define a "view" expression, which is a TLA+ state expression that produces a set of graphical elements based on the values of the variables declared in your specification. The Animation module, when used in conjunction with TLC, constructs a sequence of frames, where each frame is the value of the view expression at a step in an execution trace. The module uses SVG elements as its graphical primitives, which allows for flexibility and variety in the visualizations that can be produced. 

### Update: December 2024

These visualization features are now integrated into the web-based interface for exploring TLA+ specs found [here](https://github.com/will62794/tla-web). You can see one example of an animated spec [here](https://will62794.github.io/tla-web/#!/home?specpath=.%2Fspecs%2FCabbageGoatWolf.tla).

### Update: February 2020

The original version of this module, described below and explained in more detail [here](https://www.youtube.com/watch?v=mLF220fPrP4&t=2s), is now somewhat obsolete. TLC [now supports](https://github.com/tlaplus/tlaplus/issues/393) running trace exploration from the command line, which makes it simpler to produce TLA+ animations. The original `Animation.tla` module has been revised a bit and pushed to the CommunityModules repo as a `SVG.tla` [module](https://github.com/tlaplus/CommunityModules/blob/4a1032a541837e4775d48e5efab56ce1f026edf8/modules/SVG.tla), which provides primitives for laying out visualizations. See the [new_examples/Elevator](new_examples/Elevator) directory for a demonstration of animating a trace with this new TLC functionality. It can be done entirely from the command line with no explicit need for TLA+ Toolbox.


## How To Use

If you have an existing specification with initial state and next state predicates `Init` and `Next`, and with variables `vars`, you can define an animated version of this spec by defining the following expression:

```tla
AnimatedSpec ==
    /\ AnimatedInit(Init, View)
    /\ [][AnimatedNext(Next, View, FALSE)]_<<vars,AnimationVars>>  
```

where `View` is your defined view state expression. To produce the animation, you can set `AnimatedSpec` as the specification for TLC to check, and set up some way for TLC to produce a specific error trace. For example, you could define an invariant whose violation produces an interesting execution you would like to visualize. Or, you could just run TLC in simulation mode to see what some random execution looks like when visualized. When the error trace is produced, the state of the `svgAnimationString` variable for the final state will be a string containing a sequence of SVG elements where each is a frame of that trace. You can copy and paste this string into an HTML template and view the animation in a browser.

If you are using the TLA+ Toolbox, a convenient way to define an animation for an existing spec called `Spec.tla` is to create a new spec called `SpecAnimated.tla`. Inside `SpecAnimated.tla` you can define your view expression and any related animation operators, and define the animated version of your spec (`AnimatedSpec` as shown in the example snippet above). In order to have access to the operators and variables of your original module, and also to those of the `Animation` module you can add the directory of `Spec.tla` and `Animation.tla` to the TLA+ library path locations. You can edit these by clicking on the name of a spec in the toolbox and selecting `Properties`. Doing this will then allow you to automatically include your original module and the `Animation` module, without explicitly copying them to your new animated spec's directory. Also, any changes you make to your original spec will automatically be reflected in the version included in your animated spec.

## Related Tools

Many of the ideas behind the Animation module were inspired by the [ProB animator tool](https://www3.hhu.de/stups/prob/index.php/The_ProB_Animator_and_Model_Checker) and the [Runway specification language](https://engineering.salesforce.com/runway-intro-dc0d9578e248), both of which provide built-in visualization tools. One main goal of this module is to provide a visualization tool that is simple to use and comfortable for existing TLA+ users. This is enabled by the fact that animations can be described directly in TLA+, allowing them to take advantage of the expressiveness of the language.

