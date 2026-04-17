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

"""
    lower(net, target::ContinuousIPMTarget, transition_data)

Lower a single-state `LabelledProjectionNet` to a `ContinuousIPMProblem` by
discretizing the summed categorical transitions into a generator matrix.
"""
function CategoricalPopulationDynamics.lower(
        net::CategoricalPopulationDynamics.LabelledProjectionNet,
        target::ContinuousIPMTarget,
        transition_data::Dict{Symbol})
    state_names = CategoricalPopulationDynamics.sname(net)
    length(state_names) == 1 || error(
        "ContinuousIPMTarget lowering currently supports single-state models only")

    sn = state_names[1]
    haskey(target.domains, sn) || error("No domain for state :$sn in ContinuousIPMTarget")
    cpd = target.domains[sn]
    ipm_domain = ContinuousStatePopulationDynamics.ContinuousDomain(
        cpd.lower, cpd.upper, cpd.n_meshpoints)

    tnames = CategoricalPopulationDynamics.tname(net)
    function composed_generator(z_new, z)
        val = 0.0
        for tn in tnames
            haskey(transition_data, tn) || error("No kernel for transition :$tn")
            val += transition_data[tn](z_new, z)
        end
        return val
    end

    generator = CategoricalPopulationDynamics.left_kan_extension(composed_generator, cpd)
    generator = _apply_generator_transform(target, generator, ipm_domain, net)
    n = cpd.n_meshpoints
    u0 = isnothing(target.u0) ? ones(n) ./ n : collect(float.(target.u0))
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
        discretization = discretization,
        p = target.p,
        normalize = target.normalize,
    )
end

end # module
