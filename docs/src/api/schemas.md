# Schemas & Nets

Projection nets are the core data structures of CategoricalPopulationDynamics.jl. They represent structured population models as labelled directed graphs where nodes are life stages and edges are demographic transitions.

## Schemas

```@docs
SchProjectionNet
SchLabelledProjectionNet
```

```@example catpd
using CategoricalPopulationDynamics

net = LabelledProjectionNet(
    [:juvenile, :adult],
    :growth => (:juvenile => :adult),
    :survival => (:adult => :adult),
    :fecundity => (:adult => :juvenile),
)

typeof(net)
```

## Net Types

```@docs
ProjectionNet
LabelledProjectionNet
```

```@example catpd
(n_states(net), n_transitions(net), sname(net), tname(net))
```

## Open Nets

Open nets expose boundary ports for compositional assembly via structured cospans.

```@docs
OpenProjectionNetOb
OpenProjectionNet
OpenLabelledProjectionNetOb
OpenLabelledProjectionNet
Open
```

```@example catpd
open_net = Open(net, [1], [2])
typeof(open_net)
```

## Query Functions

```@docs
n_states
n_transitions
sources
targets
sname
tname
```

```@example catpd
(
    growth_sources = sources(net, 1),
    growth_targets = targets(net, 1),
    adult_state = sname(net, 2),
    first_transition = tname(net, 1),
)
```
