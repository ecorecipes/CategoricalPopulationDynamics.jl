# Schemas & Nets

Projection nets are the core data structures of CategoricalPopulationDynamics.jl. They represent structured population models as labelled directed graphs where nodes are life stages and edges are demographic transitions.

## Schemas

```@docs
SchProjectionNet
SchLabelledProjectionNet
```

## Net Types

```@docs
ProjectionNet
LabelledProjectionNet
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

## Query Functions

```@docs
n_states
n_transitions
sources
targets
sname
tname
```
