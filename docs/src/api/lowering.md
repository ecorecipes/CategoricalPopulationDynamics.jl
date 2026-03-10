# Lowering & Lifting

Lowering converts a categorical projection net into a concrete computational model (matrix population model or integral projection model). Lifting performs the reverse operation, reconstructing a categorical net from a concrete model.

```@docs
AbstractLoweringTarget
IPMTarget
MPMTarget
ProjectionNetTarget
lower
lift
```
