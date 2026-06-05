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

```@example catpd
using CategoricalPopulationDynamics

domain = ContinuousProjectionDomain(0.0, 1.0, 5)
ipm_target = IPMTarget(:size => domain)
mpm_target = MPMTarget()
projection_target = ProjectionNetTarget()

(
    ipm_target_is_target = ipm_target isa CategoricalPopulationDynamics.AbstractLoweringTarget,
    mpm_target_is_target = mpm_target isa CategoricalPopulationDynamics.AbstractLoweringTarget,
    projection_target_is_target = projection_target isa CategoricalPopulationDynamics.AbstractLoweringTarget,
    lower_is_function = lower isa Function,
    lift_is_function = lift isa Function,
)
```
