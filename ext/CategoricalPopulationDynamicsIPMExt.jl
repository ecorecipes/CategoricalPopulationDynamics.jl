module CategoricalPopulationDynamicsIPMExt

using CategoricalPopulationDynamics
using IntegralProjectionModels

"""
    lower(net, target::IPMTarget, transition_data)

Lower a LabelledProjectionNet to an IPMProblem.

`transition_data` is a Dict{Symbol, Function} mapping transition names to
kernel functions `(z_new, z) -> Real`.
"""
function CategoricalPopulationDynamics.lower(
        net::CategoricalPopulationDynamics.LabelledProjectionNet,
        target::IPMTarget,
        transition_data::Dict{Symbol})
    state_names = CategoricalPopulationDynamics.sname(net)
    length(state_names) == 1 || error(
        "IPMTarget lowering currently supports single-state models only")

    sn = state_names[1]
    haskey(target.domains, sn) || error("No domain for state :$sn in IPMTarget")
    cpd = target.domains[sn]
    ipm_domain = IntegralProjectionModels.ContinuousDomain(
        cpd.lower, cpd.upper, cpd.n_meshpoints)

    tnames = CategoricalPopulationDynamics.tname(net)
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
