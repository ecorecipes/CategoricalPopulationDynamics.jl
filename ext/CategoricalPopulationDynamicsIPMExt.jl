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

"""
    lower(sys::PooledProjectionSystem, target::CoupledIPMTarget)

Lower a pooled system to a `CoupledIPMProblem`. `target.p` holds the environments: a
vector with one environment per time step, or a single value used throughout.

Each component becomes a `PopulationComponent` whose model returns, each day, a
`DiscretizedKernel` of its net evaluated at the day's pools: its survival and fecundity
matrices, laid out by `state_layout(net)`. The pools, the inflows and the after-step maps
are handled as by the lowering to a `CoupledMPMProblem` (a substep named `:pools` and one
rule per component), so the two problems step the system identically. With
`stochasticity = Demographic()` the inflows are instead given to the problem as its
`inflows`, for its demographic mode to draw. Any substeps, rules, events and observables of
the target are kept, after these.
"""
function CategoricalPopulationDynamics.lower(
        sys::CategoricalPopulationDynamics.PooledProjectionSystem,
        target::CategoricalPopulationDynamics.CoupledIPMTarget)
    CPD = CategoricalPopulationDynamics
    IPM = IntegralProjectionModels
    demographic = target.stochasticity isa IPM.Demographic
    pieces = CPD._coupled_pieces(sys, target.initial_populations, target.tspan[1]; separate_inflows = demographic)

    components = Any[]
    for name in CPD.component_names(sys)
        net = sys[name]
        snames = CPD.stage_names(net)
        layout = CPD.state_layout(net)
        matrices = pieces.matrices[name]
        model = (s, day, p) -> begin
            U, F = matrices(s, day, p)
            IPM.DiscretizedKernel(U, F, layout)
        end
        metadata = get(target.metadata, name, NamedTuple())
        push!(components, name => IPM.PopulationComponent(model, target.initial_populations[name];
            stage_names = snames,
            species = CPD._metadata_get(metadata, :species, name),
            type = CPD._metadata_get(metadata, :type, :default),
            patch = CPD._metadata_get(metadata, :patch, :default)))
    end

    state = merge(pieces.state, Dict{Symbol, Any}(pairs(target.state)))
    pop_system = IPM.PopulationSystem(components...; state = state)
    return IPM.CoupledIPMProblem(pop_system, target.tspan;
        p = target.p,
        substeps = Any[pieces.substep, target.substeps...],
        rules = Any[pieces.rules..., target.rules...],
        events = collect(target.events),
        observables = collect(target.observables),
        normalize = target.normalize,
        inflows = pieces.inflows,
        stochasticity = target.stochasticity)
end

end # module
