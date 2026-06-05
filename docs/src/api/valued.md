# Valued Projection Nets

Valued projection nets associate numeric transition rates or kernel values with the transitions of a projection net, enabling direct materialization to projection matrices.

```@docs
ValuedProjectionNet
stage_names
transition_names
transition_matrix
to_matrix
```

```@example catpd
using CategoricalPopulationDynamics

vnet = ValuedProjectionNet(
    [:seed, :juvenile, :adult],
    :survival => [
        (:seed => :juvenile) => 0.4,
        (:juvenile => :adult) => 0.6,
        (:adult => :adult) => 0.9,
    ],
    :fecundity => [(:adult => :seed) => 2.5],
)

(
    stage_names = stage_names(vnet),
    transition_names = transition_names(vnet),
    survival_matrix = transition_matrix(vnet, :survival),
    full_matrix = to_matrix(vnet),
)
```
