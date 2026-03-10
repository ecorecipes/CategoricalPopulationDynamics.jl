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

## Vignettes

| # | Vignette | Description |
|---|----------|-------------|
| 1 | [Introduction to Categorical Projection Models](https://github.com/ecorecipes/CategoricalProjectionModels.jl/blob/main/vignettes/01_introduction/01_introduction.md) | Core concepts: projection nets, categorical specification of population models |
| 2 | [Kan Extensions and the IPM-MPM Adjunction](https://github.com/ecorecipes/CategoricalProjectionModels.jl/blob/main/vignettes/02_kan_extensions/02_kan_extensions.md) | Left and right Kan extensions for coarsening and refining state spaces |
| 3 | [Compositional Model Construction](https://github.com/ecorecipes/CategoricalProjectionModels.jl/blob/main/vignettes/03_composition/03_composition.md) | Composing models via undirected wiring diagrams and structured cospans |
| 4 | [Stratification and Coarsening](https://github.com/ecorecipes/CategoricalProjectionModels.jl/blob/main/vignettes/04_stratification_coarsening/04_stratification_coarsening.md) | Spatial stratification via Kronecker products |
| 5 | [Lowering and Lifting](https://github.com/ecorecipes/CategoricalProjectionModels.jl/blob/main/vignettes/05_lowering_lifting/05_lowering_lifting.md) | Converting between categorical nets and concrete matrix/IPM models |
| 6 | [Reconstructing a Published IPM from PADRINO](https://github.com/ecorecipes/CategoricalProjectionModels.jl/blob/main/vignettes/06_padrino_reconstruction/06_padrino_reconstruction.md) | Lifting a PADRINO IPM into a categorical projection net |
| 7 | [Decomposing a COMADRE Matrix Model](https://github.com/ecorecipes/CategoricalProjectionModels.jl/blob/main/vignettes/07_comadre_reconstruction/07_comadre_reconstruction.md) | Loggerhead sea turtle conservation analysis via categorical decomposition |
| 8 | [Valued Projection Nets](https://github.com/ecorecipes/CategoricalProjectionModels.jl/blob/main/vignettes/08_valued_nets/08_valued_nets.md) | Associating numeric data with transitions and materializing to matrices |
| 9 | [Environmental vs Demographic Stochasticity](https://github.com/ecorecipes/CategoricalProjectionModels.jl/blob/main/vignettes/09_stochastic_deterministic/09_stochastic_deterministic.md) | A categorical perspective on stochastic population models |
| 10 | [Time-Lagged Categorical Projection Models](https://github.com/ecorecipes/CategoricalProjectionModels.jl/blob/main/vignettes/10_time_lag/10_time_lag.md) | Functorial lag expansion with delay endofunctor |

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
