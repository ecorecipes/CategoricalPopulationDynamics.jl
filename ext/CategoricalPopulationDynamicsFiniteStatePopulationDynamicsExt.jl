module CategoricalPopulationDynamicsFiniteStatePopulationDynamicsExt

using CategoricalPopulationDynamics
using FiniteStatePopulationDynamics

function _coerce_stage_labels(labels)
    [Symbol(label) for label in labels]
end

function _default_stage_labels(n::Int)
    [Symbol("state_$i") for i in 1:n]
end

function _resolve_finite_state_domain(target::FiniteStateDynamicsTarget, n::Int; labels = nothing)
    preferred_labels = isnothing(labels) ? _default_stage_labels(n) : _coerce_stage_labels(labels)

    if isnothing(target.domain)
        return FiniteStatePopulationDynamics.DiscreteDomain(preferred_labels)
    elseif target.domain isa CategoricalPopulationDynamics.DiscreteProjectionDomain
        target.domain.n == n || throw(DimensionMismatch(
            "finite-state domain size $(target.domain.n) does not match generator size $n"))
        used_labels = isempty(target.domain.labels) ? preferred_labels : copy(target.domain.labels)
        return FiniteStatePopulationDynamics.DiscreteDomain(used_labels)
    elseif target.domain isa Integer
        Int(target.domain) == n || throw(DimensionMismatch(
            "finite-state domain size $(target.domain) does not match generator size $n"))
        return FiniteStatePopulationDynamics.DiscreteDomain(preferred_labels)
    elseif applicable(FiniteStatePopulationDynamics.n_states, target.domain)
        FiniteStatePopulationDynamics.n_states(target.domain) == n || throw(DimensionMismatch(
            "finite-state domain size $(FiniteStatePopulationDynamics.n_states(target.domain)) does not match generator size $n"))
        return target.domain
    else
        throw(ArgumentError(
            "domain $(typeof(target.domain)) is not a supported finite-state domain descriptor"))
    end
end

function _apply_generator_transform(target::FiniteStateDynamicsTarget, generator, domain, spec)
    f = target.generator_transform
    if applicable(f, generator, domain, spec)
        return f(generator, domain, spec)
    elseif applicable(f, generator, domain)
        return f(generator, domain)
    elseif applicable(f, generator)
        return f(generator)
    else
        throw(ArgumentError(
            "generator_transform $(typeof(f)) must accept (generator), (generator, domain), or (generator, domain, spec)"))
    end
end

function _normalize_delay_terms(raw, n::Int)
    raw === nothing && return nothing
    terms = FiniteStatePopulationDynamics.DelayGeneratorTerm[]
    for term in raw
        nt = if term isa FiniteStatePopulationDynamics.DelayGeneratorTerm
            term
        elseif term isa Pair
            FiniteStatePopulationDynamics.DelayGeneratorTerm(first(term), last(term))
        elseif term isa Tuple && length(term) == 2
            FiniteStatePopulationDynamics.DelayGeneratorTerm(term[1], term[2])
        else
            throw(ArgumentError(
                "delay term $(typeof(term)) must be a DelayGeneratorTerm, `lag => operator`, or (lag, operator)"))
        end
        if nt.operator isa AbstractMatrix
            size(nt.operator) == (n, n) || throw(DimensionMismatch(
                "delay operator has size $(size(nt.operator)); expected ($n, $n)"))
        end
        push!(terms, nt)
    end
    return terms
end

function _generator_problem(generator::AbstractMatrix, target::FiniteStateDynamicsTarget, spec; labels = nothing)
    size(generator, 1) == size(generator, 2) || throw(DimensionMismatch(
        "generator matrix has size $(size(generator)); expected a square matrix"))
    n = size(generator, 1)
    domain = _resolve_finite_state_domain(target, n; labels = labels)
    transformed = _apply_generator_transform(target, generator, domain, spec)
    u0 = isnothing(target.u0) ? ones(n) ./ n : collect(float.(target.u0))
    delay_terms = _normalize_delay_terms(target.delay_terms, n)
    if delay_terms !== nothing && !isempty(delay_terms)
        target.history === nothing && throw(ArgumentError(
            "FiniteStateDynamicsTarget requires `history` when `delay_terms` is non-empty"))
        return FiniteStatePopulationDynamics.DelayFiniteStateProblem(
            transformed,
            delay_terms,
            domain,
            u0,
            target.history,
            target.tspan;
            p = target.p,
            source = target.source,
            normalize = target.normalize,
            callbacks = target.callbacks)
    end
    return FiniteStatePopulationDynamics.FiniteStateGeneratorProblem(
        transformed,
        domain,
        u0,
        target.tspan;
        p = target.p,
        source = target.source,
        normalize = target.normalize,
        callbacks = target.callbacks)
end

function _sum_transition_matrices(net::CategoricalPopulationDynamics.LabelledProjectionNet,
        transition_data::Dict{Symbol, <:AbstractMatrix})
    tnames = CategoricalPopulationDynamics.tname(net)
    generator = nothing
    for tn in tnames
        haskey(transition_data, tn) || error("No matrix for transition :$tn")
        M = transition_data[tn]
        size(M, 1) == size(M, 2) || throw(DimensionMismatch(
            "transition :$tn has size $(size(M)); expected a square matrix"))
        if generator === nothing
            generator = copy(M)
        else
            size(M) == size(generator) || throw(DimensionMismatch(
                "transition :$tn has size $(size(M)); expected $(size(generator))"))
            generator .+= M
        end
    end
    generator === nothing && error("No transitions in net")
    return generator
end

"""
    lower(vnet, target::FiniteStateDynamicsTarget)

Lower a `ValuedProjectionNet` to a finite-state continuous-time generator
problem.
"""
function CategoricalPopulationDynamics.lower(
        vnet::CategoricalPopulationDynamics.ValuedProjectionNet,
        target::FiniteStateDynamicsTarget)
    generator = CategoricalPopulationDynamics.to_matrix(vnet)
    return _generator_problem(generator, target, vnet;
        labels = CategoricalPopulationDynamics.stage_names(vnet))
end

"""
    lower(net, target::FiniteStateDynamicsTarget, transition_data)

Lower a labelled categorical net with concrete transition matrices to a
finite-state continuous-time generator problem.
"""
function CategoricalPopulationDynamics.lower(
        net::CategoricalPopulationDynamics.LabelledProjectionNet,
        target::FiniteStateDynamicsTarget,
        transition_data::Dict{Symbol, <:AbstractMatrix})
    generator = _sum_transition_matrices(net, transition_data)
    labels = length(CategoricalPopulationDynamics.sname(net)) == size(generator, 1) ?
        CategoricalPopulationDynamics.sname(net) :
        nothing
    return _generator_problem(generator, target, net; labels = labels)
end

"""
    lower(net, target::FiniteStateDynamicsTarget, transition_data, stage_names)

Lower sparse transition data with explicit stage ordering to a finite-state
continuous-time generator problem.
"""
function CategoricalPopulationDynamics.lower(
        net::CategoricalPopulationDynamics.LabelledProjectionNet,
        target::FiniteStateDynamicsTarget,
        transition_data::Dict{Symbol, <:AbstractVector{<:Pair}},
        stage_names::Vector{Symbol})
    vnet = CategoricalPopulationDynamics.ValuedProjectionNet(stage_names,
        (tn => transition_data[tn] for tn in keys(transition_data))...)
    return CategoricalPopulationDynamics.lower(vnet, target)
end

"""
    lower(vnet::ValuedProjectionNet, target::DemographicFiniteStateTarget)

Lower to a demographic-stochastic `FiniteStateReactionProblem` (continuous-time
Markov jump process), building reactions via `demographic_reactions`: transition
values are per-capita rates, `fecundity`-tagged entries are births and the rest
are migrations. Solve with `solve(prob, Demographic())`.
"""
function CategoricalPopulationDynamics.lower(
        vnet::CategoricalPopulationDynamics.ValuedProjectionNet,
        target::CategoricalPopulationDynamics.DemographicFiniteStateTarget)
    reactions = CategoricalPopulationDynamics.demographic_reactions(vnet;
        fecundity = target.fecundity)
    return FiniteStatePopulationDynamics.FiniteStateReactionProblem(reactions,
        target.n0, target.tspan; p = target.p)
end

end # module
