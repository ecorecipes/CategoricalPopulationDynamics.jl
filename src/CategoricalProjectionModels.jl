module CategoricalProjectionModels

import Base: collect

using Catlab
using Catlab.CategoricalAlgebra
using Catlab.WiringDiagrams
using Catlab.WiringDiagrams.UndirectedWiringDiagrams: AbstractUWD
using LinearAlgebra
using ProjectionModels: lambda

import Catlab.WiringDiagrams: oapply

# Schemas
export SchProjectionNet, SchLabelledProjectionNet,
       ProjectionNet, LabelledProjectionNet,
       OpenProjectionNetOb, OpenProjectionNet,
       OpenLabelledProjectionNetOb, OpenLabelledProjectionNet,
       Open,
       n_states, n_transitions, sources, targets, sname, tname

# Domain types
export ContinuousProjectionDomain, DiscreteProjectionDomain,
       meshpoints, step_size, n_meshpoints, bounds,
       TransitionSpec

# Kan extensions
export left_kan_extension, right_kan_extension

# Stratification & coarsening
export stratify, coarsen

# Diagnostics
export unit_error, counit_error, adjunction_errors

# ProjectionSharer & composition
export ProjectionSharer, oapply,
       compose_transitions, compose_from_uwd

# Valued projection nets
export ValuedProjectionNet, stage_names, transition_names,
       transition_matrix, to_matrix

# Lowering/lifting
export AbstractLoweringTarget, IPMTarget, MPMTarget, ProjectionNetTarget,
       lower, lift

include("schemas.jl")
include("types.jl")
include("kan_extensions.jl")
include("stratification.jl")
include("coarsening.jl")
include("diagnostics.jl")
include("sharers.jl")
include("composition.jl")
include("valued.jl")
include("lowering.jl")

# Time-lagged models
include("time_lag.jl")
export lag_expand, lag_stratify

end # module
