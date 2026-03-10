module CategoricalProjectionModelsIPMExt

using CategoricalProjectionModels
using IntegralProjectionModels

"""
    left_kan_extension(kernel_fn, domain::ContinuousDomain)

Discretise using an IntegralProjectionModels `ContinuousDomain`.
"""
function CategoricalProjectionModels.left_kan_extension(
        kernel_fn, domain::IntegralProjectionModels.ContinuousDomain)
    cpd = ContinuousProjectionDomain(domain.lower, domain.upper, domain.n_meshpoints)
    return CategoricalProjectionModels.left_kan_extension(kernel_fn, cpd)
end

"""
    right_kan_extension(A, domain::ContinuousDomain)

Construct piecewise-constant kernel using an IntegralProjectionModels `ContinuousDomain`.
"""
function CategoricalProjectionModels.right_kan_extension(
        A::AbstractMatrix, domain::IntegralProjectionModels.ContinuousDomain)
    cpd = ContinuousProjectionDomain(domain.lower, domain.upper, domain.n_meshpoints)
    return CategoricalProjectionModels.right_kan_extension(A, cpd)
end

"""
    coarsen(A, from::ContinuousDomain, to::ContinuousDomain)

Coarsen using IntegralProjectionModels domain types.
"""
function CategoricalProjectionModels.coarsen(
        A::AbstractMatrix,
        from::IntegralProjectionModels.ContinuousDomain,
        to::IntegralProjectionModels.ContinuousDomain)
    cpd_from = ContinuousProjectionDomain(from.lower, from.upper, from.n_meshpoints)
    cpd_to = ContinuousProjectionDomain(to.lower, to.upper, to.n_meshpoints)
    return CategoricalProjectionModels.coarsen(A, cpd_from, cpd_to)
end

"""
    lower(net, target::IPMTarget, transition_data)

Lower a LabelledProjectionNet to an IPMProblem.

`transition_data` is a Dict{Symbol, Function} mapping transition names to
kernel functions `(z_new, z) -> Real`.
"""
function CategoricalProjectionModels.lower(
        net::CategoricalProjectionModels.LabelledProjectionNet,
        target::IPMTarget,
        transition_data::Dict{Symbol})
    state_names = CategoricalProjectionModels.sname(net)
    length(state_names) == 1 || error(
        "IPMTarget lowering currently supports single-state models only")

    sn = state_names[1]
    haskey(target.domains, sn) || error("No domain for state :$sn in IPMTarget")
    cpd = target.domains[sn]
    ipm_domain = IntegralProjectionModels.ContinuousDomain(
        cpd.lower, cpd.upper, cpd.n_meshpoints)

    # Compose kernel functions additively
    tnames = CategoricalProjectionModels.tname(net)
    function composed_kernel(z_new, z)
        val = 0.0
        for tn in tnames
            haskey(transition_data, tn) || error("No kernel for transition :$tn")
            val += transition_data[tn](z_new, z)
        end
        return val
    end

    n = cpd.n_meshpoints
    n0 = ones(n) ./ n
    kernel = IntegralProjectionModels.CustomKernel(composed_kernel, ipm_domain)
    return IntegralProjectionModels.IPMProblem(
        kernel, ipm_domain, n0, (0, 100))
end

end # module
