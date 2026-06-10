module CategoricalPopulationDynamicsContinuousStatePopulationDynamicsExt

using CategoricalPopulationDynamics
using ContinuousStatePopulationDynamics

function _apply_generator_transform(target::ContinuousIPMTarget, generator, domain, net)
    f = target.generator_transform
    if applicable(f, generator, domain, net)
        return f(generator, domain, net)
    elseif applicable(f, generator, domain)
        return f(generator, domain)
    elseif applicable(f, generator)
        return f(generator)
    else
        throw(ArgumentError(
            "generator_transform $(typeof(f)) must accept (generator), (generator, domain), or (generator, domain, net)"))
    end
end

_delay_lag_operator(term::ContinuousStatePopulationDynamics.DelayGeneratorTerm) =
    (term.lag, term.operator)
_delay_lag_operator(term::Pair) = (first(term), last(term))
_delay_lag_operator(term::Tuple) = length(term) == 2 ? (term[1], term[2]) :
    throw(ArgumentError("delay term tuple must be (lag, operator)"))
_delay_lag_operator(term) = throw(ArgumentError(
    "delay term $(typeof(term)) must be a DelayGeneratorTerm, `lag => operator`, or (lag, operator)"))

# Normalize categorical delay specifications into backend DelayGeneratorTerms.
# A matrix operator is used as-is; a kernel function (z_new, z) is left Kan
# extended onto the (single) state domain `cpd`, matching how the main generator
# is built. For multi-state targets `cpd` is `nothing`, so only `N × N` matrix
# operators are accepted (kernel functions have no single domain to extend over).
function _normalize_continuous_delay_terms(raw, cpd, n::Int)
    terms = ContinuousStatePopulationDynamics.DelayGeneratorTerm[]
    for term in raw
        lag, op = _delay_lag_operator(term)
        op_matrix = if op isa AbstractMatrix
            size(op) == (n, n) || throw(DimensionMismatch(
                "delay operator has size $(size(op)); expected ($n, $n)"))
            op
        elseif op isa Function
            cpd === nothing && throw(ArgumentError(
                "kernel-function delay operators are only supported for single-state " *
                "ContinuousIPMTarget; provide an $(n)×$(n) matrix for multi-state targets"))
            CategoricalPopulationDynamics.left_kan_extension(op, cpd)
        else
            throw(ArgumentError(
                "delay operator $(typeof(op)) must be an n×n matrix or a kernel function (z_new, z)"))
        end
        push!(terms, ContinuousStatePopulationDynamics.DelayGeneratorTerm(lag, op_matrix))
    end
    return terms
end

"""
    lower(net, target::ContinuousIPMTarget, transition_data)

Lower a `LabelledProjectionNet` to a `ContinuousIPMProblem` (or a
`DelayIPMProblem` when `delay_terms` are supplied) by discretizing the
categorical transitions into a generator matrix.

For a single-state net the summed transition kernels are Kan extended on the
one domain. For a multi-state net each single-source/single-target transition
kernel is Kan extended into the `(target, source)` block of a block generator,
sized and ordered to match the per-state domains in `sname(net)` order; `u0`
follows the same block layout.
"""
# Single-state: sum all transition kernels and Kan-extend on the one domain.
function _single_state_generator(net, target, transition_data, sn::Symbol)
    cpd = target.domains[sn]
    tnames = CategoricalPopulationDynamics.tname(net)
    composed_generator = function(z_new, z)
        val = 0.0
        for tn in tnames
            haskey(transition_data, tn) || error("No kernel for transition :$tn")
            val += transition_data[tn](z_new, z)
        end
        return val
    end
    generator = CategoricalPopulationDynamics.left_kan_extension(composed_generator, cpd)
    ipm_domain = ContinuousStatePopulationDynamics.ContinuousDomain(
        cpd.lower, cpd.upper, cpd.n_meshpoints)
    return generator, ipm_domain, cpd.n_meshpoints, cpd
end

# Multi-state: assemble a block generator. Block (j, i) is the Kan extension of
# the kernel of each transition from state i to state j, placed at the offset of
# the per-state domains in `sname(net)` order (the layout of `u0`).
function _multi_state_generator(net, target, transition_data, state_names)
    cpds = [target.domains[sn] for sn in state_names]
    sizes = [cpd.n_meshpoints for cpd in cpds]
    offsets = Vector{Int}(undef, length(sizes))
    acc = 0
    for k in eachindex(sizes)
        offsets[k] = acc
        acc += sizes[k]
    end
    N = acc
    G = zeros(N, N)
    for t in 1:CategoricalPopulationDynamics.n_transitions(net)
        tn = CategoricalPopulationDynamics.tname(net, t)
        haskey(transition_data, tn) || error("No kernel for transition :$tn")
        srcs = CategoricalPopulationDynamics.sources(net, t)
        tgts = CategoricalPopulationDynamics.targets(net, t)
        (length(srcs) == 1 && length(tgts) == 1) || error(
            "multi-state ContinuousIPMTarget lowering supports single-source, single-target " *
            "transitions; transition :$tn has $(length(srcs)) source(s) and $(length(tgts)) target(s)")
        i = srcs[1]
        j = tgts[1]
        block = CategoricalPopulationDynamics.left_kan_extension(
            transition_data[tn], cpds[j], cpds[i])
        ro, co = offsets[j], offsets[i]
        @view(G[(ro + 1):(ro + sizes[j]), (co + 1):(co + sizes[i])]) .+= block
    end
    domain = Dict{Symbol, ContinuousStatePopulationDynamics.ContinuousDomain}(
        sn => ContinuousStatePopulationDynamics.ContinuousDomain(
            cpds[k].lower, cpds[k].upper, cpds[k].n_meshpoints)
        for (k, sn) in enumerate(state_names))
    return G, domain, N
end

function CategoricalPopulationDynamics.lower(
        net::CategoricalPopulationDynamics.LabelledProjectionNet,
        target::ContinuousIPMTarget,
        transition_data::Dict{Symbol})
    state_names = CategoricalPopulationDynamics.sname(net)
    isempty(state_names) && error("net has no states")
    for sn in state_names
        haskey(target.domains, sn) || error("No domain for state :$sn in ContinuousIPMTarget")
    end

    if length(state_names) == 1
        generator, ipm_domain, n, delay_cpd =
            _single_state_generator(net, target, transition_data, state_names[1])
    else
        generator, ipm_domain, n = _multi_state_generator(net, target, transition_data, state_names)
        delay_cpd = nothing
    end

    generator = _apply_generator_transform(target, generator, ipm_domain, net)
    u0 = isnothing(target.u0) ? ones(n) ./ n : collect(float.(target.u0))

    if target.delay_terms !== nothing && !isempty(target.delay_terms)
        target.history === nothing && throw(ArgumentError(
            "ContinuousIPMTarget requires `history` when `delay_terms` is non-empty"))
        delay_terms = _normalize_continuous_delay_terms(target.delay_terms, delay_cpd, n)
        return ContinuousStatePopulationDynamics.DelayIPMProblem(
            generator, delay_terms, ipm_domain, u0, target.history, target.tspan;
            p = target.p,
            source = target.source,
            normalize = target.normalize)
    end

    return ContinuousStatePopulationDynamics.ContinuousIPMProblem(
        generator, ipm_domain, u0, target.tspan;
        p = target.p,
        source = target.source,
        normalize = target.normalize)
end

_pspm_term_component(term::NamedTuple, key::Symbol, default = nothing) =
    hasproperty(term, key) ? getproperty(term, key) : default
_pspm_term_component(term::AbstractDict, key::Symbol, default = nothing) =
    get(term, key, default)
_pspm_term_component(term, key::Symbol, default = nothing) = default

function _combine_spatial_pspm_terms(terms, key::Symbol)
    components = Any[]
    for term in terms
        value = _pspm_term_component(term, key, nothing)
        value === nothing || push!(components, value)
    end
    isempty(components) && return 0.0

    return function(points, population, aux, p, t)
        T = isempty(aux) ? eltype(population) : promote_type(eltype(population), eltype(aux))
        total = zeros(T, length(points))
        for component in components
            total .+= ContinuousStatePopulationDynamics._evaluate_spatial_field(
                component,
                points,
                population,
                aux,
                p,
                t,
                T;
                field_name = String(key),
            )
        end
        return total
    end
end

function _combine_boundary_pspm_terms(terms, key::Symbol)
    components = Any[]
    for term in terms
        value = _pspm_term_component(term, key, nothing)
        value === nothing || push!(components, value)
    end
    isempty(components) && return 0.0

    return function(population, aux, p, t, domain)
        T = isempty(aux) ? eltype(population) : promote_type(eltype(population), eltype(aux))
        total = zero(T)
        for component in components
            total += ContinuousStatePopulationDynamics._evaluate_boundary_flux(
                component,
                population,
                aux,
                p,
                t,
                domain,
                T;
                field_name = String(key),
            )
        end
        return total
    end
end

function _combine_auxiliary_pspm_terms(terms)
    components = Any[]
    for term in terms
        value = _pspm_term_component(term, :auxiliary_rhs, nothing)
        value === nothing || push!(components, value)
    end
    isempty(components) && return nothing

    return function(population, aux, p, t, domain)
        T = isempty(aux) ? eltype(population) : promote_type(eltype(population), eltype(aux))
        total = zeros(T, length(aux))
        for component in components
            total .+= ContinuousStatePopulationDynamics._evaluate_auxiliary_rhs(
                component,
                population,
                aux,
                p,
                t,
                domain,
                T,
            )
        end
        return total
    end
end

"""
    lower(net, target::PSPMTarget, transition_data)

Lower a single-state `LabelledProjectionNet` to a `PSPMIPMProblem` by
assembling additive transport, mortality, source, and boundary operators from
the supplied `transition_data`.
"""
function CategoricalPopulationDynamics.lower(
        net::CategoricalPopulationDynamics.LabelledProjectionNet,
        target::PSPMTarget,
        transition_data::Dict{Symbol})
    state_names = CategoricalPopulationDynamics.sname(net)
    length(state_names) == 1 || error(
        "PSPMTarget lowering currently supports single-state models only")

    sn = state_names[1]
    haskey(target.domains, sn) || error("No domain for state :$sn in PSPMTarget")
    cpd = target.domains[sn]
    ipm_domain = ContinuousStatePopulationDynamics.ContinuousDomain(
        cpd.lower, cpd.upper, cpd.n_meshpoints)

    tnames = CategoricalPopulationDynamics.tname(net)
    terms = Any[]
    for tn in tnames
        haskey(transition_data, tn) || error("No operator data for transition :$tn")
        push!(terms, transition_data[tn])
    end

    n = cpd.n_meshpoints
    u0 = isnothing(target.u0) ? ones(n) ./ n : collect(float.(target.u0))
    aux0 = collect(float.(target.aux0))
    discretization = isnothing(target.discretization) ?
        ContinuousStatePopulationDynamics.FixedMeshUpwind() :
        target.discretization

    return ContinuousStatePopulationDynamics.PSPMIPMProblem(
        ipm_domain,
        u0,
        target.tspan;
        velocity = _combine_spatial_pspm_terms(terms, :velocity),
        mortality = _combine_spatial_pspm_terms(terms, :mortality),
        source = _combine_spatial_pspm_terms(terms, :source),
        boundary_lower = _combine_boundary_pspm_terms(terms, :boundary_lower),
        boundary_upper = _combine_boundary_pspm_terms(terms, :boundary_upper),
        aux0 = aux0,
        auxiliary_rhs = _combine_auxiliary_pspm_terms(terms),
        discretization = discretization,
        p = target.p,
        normalize = target.normalize,
    )
end

end # module
