module CategoricalPopulationDynamics

import Base: collect

using Catlab
using Catlab.CategoricalAlgebra
using Catlab.WiringDiagrams
using Catlab.WiringDiagrams.UndirectedWiringDiagrams: AbstractUWD
using LinearAlgebra
using StructuredPopulationCore: lambda, ContinuousDomain,
       DemographicReaction, DemographicReactionSystem

import Catlab.WiringDiagrams: oapply
import Catlab: ⊕, evaluate

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
export left_kan_extension, right_kan_extension,
       QuadratureRule, Midpoint, Trapezoidal, Simpson,
       theoretical_error_order, theoretical_error_coefficient

# Stratification & coarsening
export stratify, coarsen

# Diagnostics
export unit_error, counit_error, adjunction_errors, convergence_analysis

# ProjectionSharer & composition
export ProjectionSharer, oapply,
       compose_transitions, compose_from_uwd

# Valued projection nets
export ValuedProjectionNet, stage_names, transition_names,
       transition_matrix, to_matrix, map_values, ⊕, ⊘

# Projection systems
export ProjectionSystemNet, component_names

# Lowering/lifting
export AbstractLoweringTarget, IPMTarget, ContinuousIPMTarget, PSPMTarget,
       FiniteStateDynamicsTarget,
       MPMTarget, StateDependentMPMTarget, ProjectionNetTarget,
       lower, lift

# Demographic stochasticity lowering
export DemographicMPMTarget, DemographicFiniteStateTarget, DemographicIPMTarget
export survival_fecundity_matrices, demographic_reactions
# Individual-based lowering
export IBMStageTarget

include("schemas.jl")
include("types.jl")
include("kan_extensions.jl")
include("stratification.jl")
include("coarsening.jl")
include("diagnostics.jl")
include("sharers.jl")
include("composition.jl")
include("valued.jl")
include("systems.jl")
include("lowering.jl")

# Time-lagged models
include("time_lag.jl")
export lag_expand, lag_stratify

# Timescale nesting
include("nesting.jl")
export TimescaleEmbedding, NestableVPN, nest, evaluate, extract_summary, ⋉

# Environmental stochasticity (Rand(C) construction)
include("rand_category.jl")
export StochasticKernelSet, n_environments, state_dim,
       dirac_embed, expected_kernel,
       stochastic_growth_rate, tuljapurkar_bound, variance_decomposition,
       ModelCubeVertex

end # module
