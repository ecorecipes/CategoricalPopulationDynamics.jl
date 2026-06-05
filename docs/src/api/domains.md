# Domain Types

Domain types describe the state spaces associated with life stages in a projection net. A domain can be continuous (for integral projection models) or discrete (for matrix population models).

```@docs
ContinuousProjectionDomain
DiscreteProjectionDomain
meshpoints
step_size
n_meshpoints
bounds
TransitionSpec
```

```@example catpd
using CategoricalPopulationDynamics

continuous_domain = ContinuousProjectionDomain(0.0, 1.0, 4)
discrete_domain = DiscreteProjectionDomain([:seed, :adult])
spec = TransitionSpec(:survival, 0.85)

(
    meshpoints = meshpoints(continuous_domain),
    step = step_size(continuous_domain),
    n_discrete = n_meshpoints(discrete_domain),
    bounds = bounds(continuous_domain),
    transition_name = spec.name,
)
```
