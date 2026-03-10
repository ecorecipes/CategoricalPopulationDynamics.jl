# CategoricalProjectionModels.jl

A Julia package for categorical and functorial approaches to structured population models, built on [Catlab.jl](https://github.com/AlgebraicJulia/Catlab.jl).

## Features

- **Projection nets**: `LabelledProjectionNet` and `ValuedProjectionNet` for categorical specification of population models
- **Kan extensions**: left and right Kan extensions for coarsening and refining state spaces
- **Stratification**: spatial stratification via Kronecker products, with commutativity guarantees
- **Composition**: compose models via undirected wiring diagrams and structured cospans
- **Time-lagged models**: functorial lag expansion (`lag_expand`) with delay endofunctor
- **Lowering/lifting**: convert between categorical nets and concrete matrix/IPM models

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
println("λ = ", lambda(A))

# Time-lag expansion
vnet_lag = lag_expand(vnet, Dict(:fecundity => 1))
A_lag = to_matrix(vnet_lag)
println("Lagged λ = ", lambda(A_lag))
```

## Installation

This package is not yet registered in the Julia General registry. Install directly from GitHub (the [ProjectionModels.jl](https://github.com/ecorecipes/ProjectionModels.jl) dependency must be installed first):

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

## Related

- [ProjectionModels.jl](https://github.com/ecorecipes/ProjectionModels.jl) — shared abstractions
- [MatrixProjectionModels.jl](https://github.com/ecorecipes/MatrixProjectionModels.jl) — discrete-stage matrix models
- [IntegralProjectionModels.jl](https://github.com/ecorecipes/IntegralProjectionModels.jl) — continuous-state IPMs
- [Catlab.jl](https://github.com/AlgebraicJulia/Catlab.jl) — applied category theory
