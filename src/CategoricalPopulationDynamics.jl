module CategoricalPopulationDynamics

import Base: collect

using Catlab
using Catlab.CategoricalAlgebra
using Catlab.WiringDiagrams
using Catlab.WiringDiagrams.UndirectedWiringDiagrams: AbstractUWD, ports_with_junction, ports
using LinearAlgebra
using StructuredPopulationCore: lambda, ContinuousDomain, DiscreteDomain,
       DemographicReaction, DemographicReactionSystem,
       AbstractStochasticity, Deterministic, Demographic
import StructuredPopulationCore

import Catlab.WiringDiagrams: oapply
import Catlab: ⊕, evaluate
# Open communities compose along undirected wiring diagrams with a method of Catlab's
# `compose`, and report the diagram with a method of Catlab's `diagram`, so that the names
# mean one function whether or not Catlab is loaded alongside.
import Catlab: compose, diagram
using Catlab: UndirectedWiringDiagram, RelationDiagram, nparts, subpart, junction,
              add_box!, add_junctions!, set_junction!
# Functions that the core package also has are extended here, for this package's domains, nets
# and Catlab types, instead of being defined again under the same name. Each is then one
# function across the stack, usable unqualified whichever packages are loaded together:
# the accessors of a discretised domain, the count of states, the stochastic growth rate, and
# the operations between kernels and matrices (whose methods for the core package's own
# `ContinuousDomain` and for plain matrices live in StructuredPopulationCore).
import StructuredPopulationCore: meshpoints, step_size, bounds, n_states, stochastic_growth_rate,
    left_kan_extension, right_kan_extension, stratify, coarsen, compose_from_uwd, discretise_kernel

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
       MPMTarget, StateDependentMPMTarget, CoupledIPMTarget, ProjectionNetTarget,
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

# Stage durations and stratification of named nets
include("stage_structure.jl")
export expand_stage, expand_stages, stratum_stage, stratum_transition

# Responsive nets and pooled systems (communities)
include("responsive.jl")
export StageVector, ResponseContext, ResponsiveProjectionNet,
       respond, inflow, after_step, births, context, meshes, state_layout,
       Pool, PooledProjectionSystem, pool_names, pool_totals, advance, trajectory

# Open communities: pooled systems composed along undirected wiring diagrams
include("open_communities.jl")
export OpenCommunity, species, community, compose, system, species_names, diagram,
       subcommunity, state_vector

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
