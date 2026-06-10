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
# Demographic stochasticity: move-vs-birth resolution + targets
# ---------------------------------------------------------------------------

"""
    survival_fecundity_matrices(vnet; fecundity = Symbol[])

Split a `ValuedProjectionNet` into a survival/transition matrix `U` and a
fecundity matrix `F` by summing each transition's matrix into `F` if its name is
listed in `fecundity` and into `U` otherwise. `U` feeds the Multinomial
survival/movement draw and `F` the Poisson birth draw of a discrete-time
demographic realization; `U + F == to_matrix(vnet)`.
"""
function survival_fecundity_matrices(vnet::ValuedProjectionNet; fecundity = Symbol[])
    fec = Set(Symbol.(fecundity))
    n = length(stage_names(vnet))
    U = zeros(Float64, n, n)
    F = zeros(Float64, n, n)
    for tn in transition_names(vnet)
        M = transition_matrix(vnet, tn)
        if tn in fec
            F .+= M
        else
            U .+= M
        end
    end
    return U, F
end

_demographic_propensity(coef, i) = (n, p, t) -> coef * n[i]

"""
    demographic_reactions(vnet; fecundity = Symbol[])

Build a continuous-time `DemographicReactionSystem` from a `ValuedProjectionNet`
by interpreting each transition value as a per-capita rate. Entries of a
**fecundity** transition `(from => to) => r` become **birth** reactions
(`+e_to` at rate `r·n_from`; the parent persists). Entries of other transitions
`(from => to) => r` with `from ≠ to` become **migration** reactions
(`-e_from + e_to`); `from == to` entries are skipped (no event in continuous
time). Model death as migration to an absorbing stage.
"""
function demographic_reactions(vnet::ValuedProjectionNet; fecundity = Symbol[])
    fec = Set(Symbol.(fecundity))
    snames = stage_names(vnet)
    n = length(snames)
    idx = Dict(s => i for (i, s) in enumerate(snames))
    reactions = DemographicReaction[]
    for tn in transition_names(vnet)
        isfec = tn in fec
        for pr in vnet.transition_values[tn]
            from, to = pr.first.first, pr.first.second
            val = pr.second
            val == 0 && continue
            i = idx[from]
            j = idx[to]
            if isfec
                push!(reactions, DemographicReaction(_demographic_propensity(val, i), n, j => +1))
            elseif i != j
                push!(reactions, DemographicReaction(_demographic_propensity(val, i), n,
                    i => -1, j => +1))
            end
        end
    end
    return DemographicReactionSystem(n, reactions)
end

"""
    DemographicMPMTarget(n0, tspan; fecundity = Symbol[], p = nothing)

Target for lowering a `ValuedProjectionNet` to a demographic-stochastic
`MPMProblem` (discrete time): survival/transition values become the Multinomial
matrix `U` and `fecundity`-tagged values the Poisson matrix `F`. Requires the
MatrixProjectionModels extension. Solve with `solve(prob, DirectIteration())`.
"""
struct DemographicMPMTarget{N, P, F} <: AbstractLoweringTarget
    n0::N
    tspan::Tuple{Int, Int}
    fecundity::F
    p::P
end

function DemographicMPMTarget(n0, tspan::Tuple{<:Integer, <:Integer};
        fecundity = Symbol[], p = nothing)
    return DemographicMPMTarget(collect(n0), (Int(tspan[1]), Int(tspan[2])),
        collect(Symbol, fecundity), p)
end

"""
    DemographicIPMTarget(domains; n0, tspan, fecundity = Symbol[], rule = :midpoint, p = nothing)

Target for lowering a single-state `LabelledProjectionNet` of continuous kernels
to a **binned** demographic-stochastic discrete-time problem. The non-`fecundity`
transition kernels are summed and Kan-extended into a sub-stochastic
survival/growth matrix `P` (Multinomial draw); the `fecundity` kernels into a
fecundity matrix `F` (Poisson draw). Since the discretized model is a matrix
demographic model over mesh bins, this produces an `MPMProblem` with
`Demographic()` stochasticity (requires the MatrixProjectionModels extension).
Solve with `solve(prob, DirectIteration())`.
"""
struct DemographicIPMTarget{N, P, F} <: AbstractLoweringTarget
    domains::Dict{Symbol, ContinuousProjectionDomain}
    n0::N
    tspan::Tuple{Int, Int}
    fecundity::F
    rule::Symbol
    p::P
end

function DemographicIPMTarget(domains::AbstractDict{Symbol}; n0, tspan,
        fecundity = Symbol[], rule::Symbol = :midpoint, p = nothing)
    return DemographicIPMTarget(
        Dict{Symbol, ContinuousProjectionDomain}(name => dom for (name, dom) in pairs(domains)),
        collect(n0), (Int(tspan[1]), Int(tspan[2])), collect(Symbol, fecundity), rule, p)
end

DemographicIPMTarget(pairs::Pair...; kwargs...) = DemographicIPMTarget(Dict(pairs...); kwargs...)

"""
    DemographicFiniteStateTarget(n0, tspan; fecundity = Symbol[], p = nothing)

Target for lowering a `ValuedProjectionNet` to a demographic-stochastic
`FiniteStateReactionProblem` (continuous-time Markov jump process), using
[`demographic_reactions`](@ref) (transition values are per-capita rates).
Requires the FiniteStatePopulationDynamics extension. Solve with
`solve(prob, Demographic())`.
"""
struct DemographicFiniteStateTarget{N, T<:Real, P, F} <: AbstractLoweringTarget
    n0::N
    tspan::Tuple{T, T}
    fecundity::F
    p::P
end

function DemographicFiniteStateTarget(n0, tspan::Tuple{<:Real, <:Real};
        fecundity = Symbol[], p = nothing)
    return DemographicFiniteStateTarget(collect(n0), (float(tspan[1]), float(tspan[2])),
        collect(Symbol, fecundity), p)
end

"""
    IBMStageTarget(stages0; fecundity = Symbol[], death = nothing, rng = nothing)

Target for lowering a `ValuedProjectionNet` of per-stage rates to an *individual-
based* stage-structured continuous-time realization (an Ark ECS world; requires
the IndividualBasedPopulationDynamics extension). Non-`fecundity` transitions
become inter-stage movements, `fecundity`-tagged transitions become births
(offspring in the target stage), and `death` is a per-stage mortality-rate vector
(default zeros). `stages0` is the initial count per stage; one entity is spawned
per individual. Realize with `IndividualBasedPopulationDynamics.ibm_run_stage!`.
"""
struct IBMStageTarget{S, D, F, R} <: AbstractLoweringTarget
    stages0::S
    death::D
    fecundity::F
    rng::R
end

function IBMStageTarget(stages0; fecundity = Symbol[], death = nothing, rng = nothing)
    return IBMStageTarget(collect(Int, stages0), death, collect(Symbol, fecundity), rng)
end

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
