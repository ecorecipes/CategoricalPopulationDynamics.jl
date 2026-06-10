"""
Lowering/lifting stubs for converting between categorical specifications
and concrete projection model objects.

Concrete implementations are provided by package extensions
(`CategoricalPopulationDynamicsIPMExt`,
`CategoricalPopulationDynamicsContinuousStatePopulationDynamicsExt`, and
`CategoricalPopulationDynamicsMPMExt`).
"""

# ---------------------------------------------------------------------------
# Abstract target types
# ---------------------------------------------------------------------------

"""Abstract base for lowering targets."""
abstract type AbstractLoweringTarget end

"""
    IPMTarget

Target for lowering a ProjectionNet to an `IPMProblem`.
Requires domain specifications for each state variable.
"""
struct IPMTarget <: AbstractLoweringTarget
    domains::Dict{Symbol, ContinuousProjectionDomain}
end

IPMTarget(pairs::Pair{Symbol}...) = IPMTarget(Dict(pairs...))

"""
    ContinuousIPMTarget(domains; kwargs...)

Target for lowering a `LabelledProjectionNet` to a continuous-time
`ContinuousIPMProblem` in `ContinuousStatePopulationDynamics.jl`.

Keyword arguments:

- `u0`: initial population vector (defaults to a uniform distribution)
- `tspan`: continuous-time span for the ODE problem
- `p`: parameters passed through to the concrete problem
- `source`: optional inhomogeneous source term
- `generator_transform`: optional transform applied to the lowered generator
- `normalize`: whether to project derivatives onto a mass-preserving tangent
  direction
- `delay_terms`: optional collection of delayed linear contributions. If
  non-empty, the target lowers to a `DelayIPMProblem` instead of a
  `ContinuousIPMProblem`. Each term may be a `DelayGeneratorTerm`, a
  `lag => operator` pair, or a `(lag, operator)` tuple. The `operator` may be an
  `n × n` matrix (used as-is) or a kernel function `(z_new, z) -> Real` (left
  Kan extended onto the state domain like the main generator).
- `history`: history function for delay problems (required when `delay_terms` is
  non-empty). Called as `history(p, t)` and must return a state vector matching
  `u0`.
"""
struct ContinuousIPMTarget{U, T<:Real, P, S, F, DT, H} <: AbstractLoweringTarget
    domains::Dict{Symbol, ContinuousProjectionDomain}
    u0::U
    tspan::Tuple{T, T}
    p::P
    source::S
    generator_transform::F
    normalize::Bool
    delay_terms::DT
    history::H
end

function ContinuousIPMTarget(domains::AbstractDict{Symbol, <:ContinuousProjectionDomain};
        u0 = nothing,
        tspan::Tuple{<:Real, <:Real} = (0.0, 1.0),
        p = nothing,
        source = nothing,
        generator_transform = identity,
        normalize::Bool = false,
        delay_terms = nothing,
        history = nothing)
    tspan[2] >= tspan[1] || throw(ArgumentError("tspan must satisfy tspan[2] >= tspan[1]"))
    if delay_terms !== nothing && !isempty(delay_terms) && history === nothing
        throw(ArgumentError(
            "ContinuousIPMTarget requires `history` when `delay_terms` is non-empty"))
    end
    return ContinuousIPMTarget(
        Dict{Symbol, ContinuousProjectionDomain}(name => domain for (name, domain) in pairs(domains)),
        u0,
        (float(tspan[1]), float(tspan[2])),
        p,
        source,
        generator_transform,
        normalize,
        delay_terms,
        history)
end

function ContinuousIPMTarget(pairs::Pair...; kwargs...)
    return ContinuousIPMTarget(Dict(pairs...); kwargs...)
end

"""
    PSPMTarget(domains; kwargs...)

Target for lowering a single-state `LabelledProjectionNet` to a
`PSPMIPMProblem` in `ContinuousStatePopulationDynamics.jl`.

The corresponding `transition_data` entries should provide named-tuples or
dictionaries with any of:

- `velocity`
- `mortality`
- `source`
- `boundary_lower`
- `boundary_upper`
- `auxiliary_rhs` — derivative of the coupled auxiliary ODE state, called as
  `(population, aux, p, t, domain)` and returning a vector matching `aux0`
  (other backend-supported signatures are also accepted)

Contributions for each key are summed additively across transitions.

Keyword arguments:

- `u0`: initial population density on the discretized trait mesh
- `aux0`: optional auxiliary ODE state appended after the population density
- `tspan`: continuous-time span for the PSPM solve
- `p`: parameters passed through to the concrete problem
- `discretization`: transport discretization object
  (resolved by the ContinuousStatePopulationDynamics extension)
- `normalize`: whether to project the population derivative onto a mass-preserving
  tangent direction
"""
struct PSPMTarget{U, A, T<:Real, P, D} <: AbstractLoweringTarget
    domains::Dict{Symbol, ContinuousProjectionDomain}
    u0::U
    aux0::A
    tspan::Tuple{T, T}
    p::P
    discretization::D
    normalize::Bool
end

function PSPMTarget(domains::AbstractDict{Symbol, <:ContinuousProjectionDomain};
        u0 = nothing,
        aux0 = Float64[],
        tspan::Tuple{<:Real, <:Real} = (0.0, 1.0),
        p = nothing,
        discretization = nothing,
        normalize::Bool = false)
    tspan[2] >= tspan[1] || throw(ArgumentError("tspan must satisfy tspan[2] >= tspan[1]"))
    return PSPMTarget(
        Dict{Symbol, ContinuousProjectionDomain}(name => domain for (name, domain) in pairs(domains)),
        u0,
        collect(aux0),
        (float(tspan[1]), float(tspan[2])),
        p,
        discretization,
        normalize)
end

function PSPMTarget(pairs::Pair...; kwargs...)
    return PSPMTarget(Dict(pairs...); kwargs...)
end

"""
    FiniteStateDynamicsTarget(; kwargs...)

Target for lowering a discrete-state categorical specification to a
`FiniteStateGeneratorProblem` in `FiniteStatePopulationDynamics.jl`, or to
a `DelayFiniteStateProblem` when delay terms are supplied.

Keyword arguments:

- `domain`: optional finite-state domain descriptor used to name/validate states
- `u0`: initial state vector (defaults to a uniform distribution)
- `tspan`: continuous-time span for the ODE problem
- `p`: parameters passed through to the concrete problem
- `source`: optional inhomogeneous source term
- `generator_transform`: optional transform applied to the lowered generator
- `normalize`: whether to project derivatives onto a mass-preserving tangent
  direction
- `delay_terms`: optional collection of `DelayGeneratorTerm`s. If non-empty, the
  target lowers to a `DelayFiniteStateProblem` instead of a
  `FiniteStateGeneratorProblem`.
- `history`: history function for delay problems (required when
  `delay_terms` is non-empty). Called as `history(p, t)` and must return a
  state vector matching `u0`.
- `callbacks`: optional SciML callback or `CallbackSet` attached to the lowered
  problem. Use the helpers in `FiniteStatePopulationDynamics` (e.g.
  `scheduled_event`, `periodic_event`, `threshold_event`) to build them.
"""
struct FiniteStateDynamicsTarget{D, U, T<:Real, P, S, F, DT, H, C} <: AbstractLoweringTarget
    domain::D
    u0::U
    tspan::Tuple{T, T}
    p::P
    source::S
    generator_transform::F
    normalize::Bool
    delay_terms::DT
    history::H
    callbacks::C
end

function FiniteStateDynamicsTarget(;
        domain = nothing,
        u0 = nothing,
        tspan::Tuple{<:Real, <:Real} = (0.0, 1.0),
        p = nothing,
        source = nothing,
        generator_transform = identity,
        normalize::Bool = false,
        delay_terms = nothing,
        history = nothing,
        callbacks = nothing)
    tspan[2] >= tspan[1] || throw(ArgumentError("tspan must satisfy tspan[2] >= tspan[1]"))
    if delay_terms !== nothing && !isempty(delay_terms) && history === nothing
        throw(ArgumentError(
            "FiniteStateDynamicsTarget requires `history` when `delay_terms` is non-empty"))
    end
    return FiniteStateDynamicsTarget(
        domain,
        u0,
        (float(tspan[1]), float(tspan[2])),
        p,
        source,
        generator_transform,
        normalize,
        delay_terms,
        history,
        callbacks)
end

"""
    MPMTarget

Target for lowering a ProjectionNet to a `MatrixProjectionModel`.
"""
struct MPMTarget <: AbstractLoweringTarget end

"""
    StateDependentMPMTarget(initial_populations, tspan; kwargs...)

Target for lowering a `ProjectionSystemNet` (or a single valued/nested net) to a
`CoupledMPMProblem` in `MatrixProjectionModels.jl`.

Keyword arguments:

- `p`: parameters passed through to the concrete problem
- `substeps`, `rules`, `events`, `observables`: MPM-side execution semantics
- `metadata`: per-component NamedTuples / Dicts with `species`, `type`, and `patch`
- `state`: auxiliary mutable state for the lowered `PopulationSystem`
- `component_transforms`: optional per-component functions
  `(base_model, system, day, p) -> matrix_or_mpm`
- `normalize`: whether to normalize each component after each update
"""
struct StateDependentMPMTarget{N, P, S, R, E, O, M, St, C} <: AbstractLoweringTarget
    initial_populations::N
    tspan::Tuple{Int, Int}
    p::P
    substeps::S
    rules::R
    events::E
    observables::O
    metadata::M
    state::St
    component_transforms::C
    normalize::Bool
end

function StateDependentMPMTarget(initial_populations::AbstractDict{Symbol, <:AbstractVector},
        tspan::Tuple{Int, Int};
        p = nothing,
        substeps = (),
        rules = (),
        events = (),
        observables = (),
        metadata = Dict{Symbol, NamedTuple}(),
        state = NamedTuple(),
        component_transforms = Dict{Symbol, Function}(),
        normalize::Bool = false)
    tspan[2] >= tspan[1] || throw(ArgumentError("tspan must satisfy tspan[2] >= tspan[1]"))
    copied_populations = Dict{Symbol, AbstractVector}(name => copy(pop) for (name, pop) in pairs(initial_populations))
    return StateDependentMPMTarget(
        copied_populations,
        tspan,
        p,
        collect(substeps),
        collect(rules),
        collect(events),
        collect(observables),
        metadata,
        state,
        component_transforms,
        normalize)
end

function StateDependentMPMTarget(tspan::Tuple{Int, Int},
        populations::Pair{Symbol, <:AbstractVector}...;
        kwargs...)
    return StateDependentMPMTarget(Dict(populations), tspan; kwargs...)
end

"""
    ProjectionNetTarget

Target for lifting a concrete model back to a `LabelledProjectionNet`.
"""
struct ProjectionNetTarget <: AbstractLoweringTarget end

# ---------------------------------------------------------------------------
# Function stubs (extended by package extensions)
# ---------------------------------------------------------------------------

"""
    lower(net::LabelledProjectionNet, target::AbstractLoweringTarget, transition_data)

Lower a categorical projection net specification to a concrete model object.

- `IPMTarget`: produces an `IPMProblem` (requires IntegralProjectionModels extension)
- `ContinuousIPMTarget`: produces a `ContinuousIPMProblem`, or a
  `DelayIPMProblem` when `delay_terms` are supplied
  (requires ContinuousStatePopulationDynamics extension)
- `PSPMTarget`: produces a `PSPMIPMProblem`
  (requires ContinuousStatePopulationDynamics extension)
- `FiniteStateDynamicsTarget`: produces a `FiniteStateGeneratorProblem`
  (requires FiniteStatePopulationDynamics extension)
- `MPMTarget`: produces a `MatrixProjectionModel` (requires MatrixProjectionModels extension)
- `StateDependentMPMTarget`: produces a `CoupledMPMProblem` (requires MatrixProjectionModels extension)
"""
function lower end

"""
    lift(model, target::ProjectionNetTarget)

Lift a concrete model object back to a `LabelledProjectionNet`.

- From `MatrixProjectionModel`: extracts states and transitions
"""
function lift end
