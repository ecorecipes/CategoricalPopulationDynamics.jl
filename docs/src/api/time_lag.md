# Time-Lag Models

Time-lag operations introduce reproductive delays into projection models via a functorial delay endofunctor. The lag expansion adds intermediate "waiting" stages that represent the passage of time before a delayed transition fires.

```@docs
lag_expand
lag_stratify
```

```@example catpd
using CategoricalPopulationDynamics
using StructuredPopulationCore: TimeLagStructure

net = LabelledProjectionNet(
    [:juvenile, :adult],
    :survival => (:adult => :adult),
    :fecundity => (:adult => :juvenile),
)
lagged_net = lag_expand(net, Dict(:fecundity => 1))

components = [
    [0.6 0.0; 0.2 0.8],
    [0.0 0.7; 0.0 0.0],
]
dispersal = [0.9 0.1; 0.2 0.8]
lagged_stratified = lag_stratify(components, dispersal, TimeLagStructure(1))

(
    states = sname(lagged_net),
    transitions = tname(lagged_net),
    stratified_size = size(lagged_stratified),
)
```
