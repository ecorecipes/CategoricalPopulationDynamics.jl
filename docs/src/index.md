# CategoricalProjectionModels.jl

A Julia package for categorical and functorial approaches to structured population models, built on [Catlab.jl](https://github.com/AlgebraicJulia/Catlab.jl).

## Overview

CategoricalProjectionModels.jl provides a mathematical framework for specifying, composing, and transforming structured population models using applied category theory. Population models are represented as *projection nets* — labelled Petri-net-like structures whose transitions carry demographic kernels — and manipulated via functorial operations such as Kan extensions, stratification, and compositional assembly.

Key capabilities include:

- **Projection nets**: `LabelledProjectionNet` and `ValuedProjectionNet` for categorical specification of population models with named stages and transitions.
- **Kan extensions**: left and right Kan extensions for systematically coarsening and refining state spaces, establishing a formal adjunction between IPMs and MPMs.
- **Stratification**: spatial or environmental stratification via Kronecker products, with commutativity guarantees.
- **Composition**: assemble complex models from simpler components using undirected wiring diagrams and structured cospans.
- **Time-lagged models**: functorial lag expansion (`lag_expand`) with a delay endofunctor for modelling reproductive delays.
- **Lowering and lifting**: convert between categorical nets and concrete matrix population models or integral projection models.

## Quick Start

```julia
using CategoricalProjectionModels
using ProjectionModels: lambda

# Define a valued projection net
vnet = ValuedProjectionNet([:seed, :small, :large],
    :survival => [(:seed => :small) => 0.2, (:small => :large) => 0.4,
                  (:small => :small) => 0.3, (:large => :large) => 0.7],
    :fecundity => [(:large => :seed) => 5.0, (:small => :seed) => 1.0])

# Materialize to a projection matrix
A = to_matrix(vnet)
println("lambda = ", lambda(A))

# Time-lag expansion
vnet_lag = lag_expand(vnet, Dict(:fecundity => 1))
A_lag = to_matrix(vnet_lag)
println("Lagged lambda = ", lambda(A_lag))
```

## Installation

This package is not yet registered in the Julia General registry. Install directly from GitHub:

```julia
using Pkg
Pkg.add(url="https://github.com/ecorecipes/ProjectionModels.jl")
Pkg.add(url="https://github.com/ecorecipes/CategoricalProjectionModels.jl")
```

To enable the optional extensions for matrix and integral projection model interop, also install:

```julia
Pkg.add(url="https://github.com/ecorecipes/MatrixProjectionModels.jl")
Pkg.add(url="https://github.com/ecorecipes/IntegralProjectionModels.jl")
```

## Related Packages

- [ProjectionModels.jl](https://github.com/ecorecipes/ProjectionModels.jl) — shared abstractions for projection models
- [MatrixProjectionModels.jl](https://github.com/ecorecipes/MatrixProjectionModels.jl) — discrete-stage matrix population models
- [IntegralProjectionModels.jl](https://github.com/ecorecipes/IntegralProjectionModels.jl) — continuous-state integral projection models
- [Catlab.jl](https://github.com/AlgebraicJulia/Catlab.jl) — applied category theory in Julia
