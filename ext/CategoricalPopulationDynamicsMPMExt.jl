module CategoricalPopulationDynamicsMPMExt

using CategoricalPopulationDynamics
using MatrixProjectionModels

"""
    lower(net, target::MPMTarget, transition_data)

Lower a LabelledProjectionNet to a MatrixProjectionModel.

`transition_data` is a Dict{Symbol, Matrix} mapping transition names to
sub-matrices. The full projection matrix is their additive sum.
"""
function CategoricalPopulationDynamics.lower(
        net::CategoricalPopulationDynamics.LabelledProjectionNet,
        target::MPMTarget,
        transition_data::Dict{Symbol, <:AbstractMatrix})
    tnames = CategoricalPopulationDynamics.tname(net)
    A = nothing
    for tn in tnames
        haskey(transition_data, tn) || error("No matrix for transition :$tn")
        M = transition_data[tn]
        A = A === nothing ? copy(M) : A .+ M
    end
    A === nothing && error("No transitions in net")
    return MatrixProjectionModels.MatrixProjectionModel(A)
end

"""
    lift(mpm::MatrixProjectionModel, target::ProjectionNetTarget)

Lift a MatrixProjectionModel back to a LabelledProjectionNet.

Creates a single state `:stage` and a single transition `:A` since
the decomposition into sub-transitions is not recoverable from a matrix alone.
"""
function CategoricalPopulationDynamics.lift(
        mpm::MatrixProjectionModels.MatrixProjectionModel,
        target::ProjectionNetTarget)
    # Create a net with one aggregate state and one transition
    # (sub-transition decomposition is not recoverable from the aggregated matrix)
    net = CategoricalPopulationDynamics.LabelledProjectionNet(
        [:population],
        :projection => (:population => :population))
    return net
end

"""
    lower(vnet::ValuedProjectionNet, target::MPMTarget)

Lower a ValuedProjectionNet directly to a MatrixProjectionModel.
The full projection matrix is the additive sum of all transition matrices.
"""
function CategoricalPopulationDynamics.lower(
        vnet::CategoricalPopulationDynamics.ValuedProjectionNet,
        target::MPMTarget)
    A = CategoricalPopulationDynamics.to_matrix(vnet)
    snames = CategoricalPopulationDynamics.stage_names(vnet)
    return MatrixProjectionModels.MatrixProjectionModel(A; stage_names=snames)
end

function _metadata_get(meta::NamedTuple, key::Symbol, default)
    hasproperty(meta, key) ? getproperty(meta, key) : default
end

function _metadata_get(meta::AbstractDict, key::Symbol, default)
    get(meta, key, default)
end

_metadata_get(meta, key::Symbol, default) = default

function _single_component_name(target::CategoricalPopulationDynamics.StateDependentMPMTarget)
    names = collect(keys(target.initial_populations))
    length(names) == 1 && return only(names)
    :population in names && return :population
    throw(ArgumentError(
        "Lowering a single projection net to StateDependentMPMTarget requires exactly one initial population or a :population key"))
end

function _lowered_component(spec, target::CategoricalPopulationDynamics.StateDependentMPMTarget, name::Symbol)
    metadata = get(target.metadata, name, NamedTuple())
    species = _metadata_get(metadata, :species, name)
    component_type = _metadata_get(metadata, :type, :default)
    patch = _metadata_get(metadata, :patch, :default)

    A = CategoricalPopulationDynamics.to_matrix(spec)
    snames = CategoricalPopulationDynamics.stage_names(spec)
    mpm = MatrixProjectionModels.MatrixProjectionModel(A; stage_names=snames)
    model = if haskey(target.component_transforms, name)
        transform = target.component_transforms[name]
        (sys, day, p) -> transform(mpm, sys, day, p)
    else
        mpm
    end

    return MatrixProjectionModels.PopulationComponent(model, target.initial_populations[name];
        stage_names = snames,
        species = species,
        type = component_type,
        patch = patch)
end

function CategoricalPopulationDynamics.lower(
        sys::CategoricalPopulationDynamics.ProjectionSystemNet,
        target::CategoricalPopulationDynamics.StateDependentMPMTarget)
    system_names = Set(CategoricalPopulationDynamics.component_names(sys))
    target_names = Set(keys(target.initial_populations))
    system_names == target_names || throw(ArgumentError(
        "ProjectionSystemNet components $(collect(CategoricalPopulationDynamics.component_names(sys))) " *
        "do not match initial_populations keys $(collect(keys(target.initial_populations)))"))

    component_pairs = Any[]
    for name in CategoricalPopulationDynamics.component_names(sys)
        push!(component_pairs, name => _lowered_component(sys[name], target, name))
    end

    pop_system = MatrixProjectionModels.PopulationSystem(component_pairs...; state=target.state)
    return MatrixProjectionModels.CoupledMPMProblem(pop_system, target.tspan;
        p = target.p,
        substeps = target.substeps,
        rules = target.rules,
        events = target.events,
        observables = target.observables,
        normalize = target.normalize)
end

function CategoricalPopulationDynamics.lower(
        vnet::CategoricalPopulationDynamics.ValuedProjectionNet,
        target::CategoricalPopulationDynamics.StateDependentMPMTarget)
    name = _single_component_name(target)
    return CategoricalPopulationDynamics.lower(
        CategoricalPopulationDynamics.ProjectionSystemNet(name => vnet),
        target)
end

function CategoricalPopulationDynamics.lower(
        vnet::CategoricalPopulationDynamics.NestableVPN,
        target::CategoricalPopulationDynamics.StateDependentMPMTarget)
    name = _single_component_name(target)
    return CategoricalPopulationDynamics.lower(
        CategoricalPopulationDynamics.ProjectionSystemNet(name => vnet),
        target)
end

"""
    lower(net::LabelledProjectionNet, target::MPMTarget, transition_data, stage_names)

Lower a LabelledProjectionNet with sparse transition data to a MatrixProjectionModel.

`transition_data` is a `Dict{Symbol, Vector{Pair{Pair{Symbol,Symbol}, <:Real}}}`.
`stage_names` is a `Vector{Symbol}` of ordered stage labels.
"""
function CategoricalPopulationDynamics.lower(
        net::CategoricalPopulationDynamics.LabelledProjectionNet,
        target::MPMTarget,
        transition_data::Dict{Symbol, <:AbstractVector{<:Pair}},
        stage_names::Vector{Symbol})
    vnet = CategoricalPopulationDynamics.ValuedProjectionNet(stage_names,
        (tn => transition_data[tn] for tn in keys(transition_data))...)
    return CategoricalPopulationDynamics.lower(vnet, target)
end

"""
    lower(vnet::ValuedProjectionNet, target::DemographicMPMTarget)

Lower to a demographic-stochastic `MPMProblem`: the `fecundity`-tagged
transitions form the Poisson matrix `F` and the rest the Multinomial
survival/transition matrix `U` (`A = U + F`). Solve with
`solve(prob, DirectIteration())` for one realization, or `demographic_ensemble`.
"""
function CategoricalPopulationDynamics.lower(
        vnet::CategoricalPopulationDynamics.ValuedProjectionNet,
        target::CategoricalPopulationDynamics.DemographicMPMTarget)
    U, F = CategoricalPopulationDynamics.survival_fecundity_matrices(vnet;
        fecundity = target.fecundity)
    snames = CategoricalPopulationDynamics.stage_names(vnet)
    mpm = MatrixProjectionModels.MatrixProjectionModel(U, F; stage_names = snames)
    return MatrixProjectionModels.MPMProblem(MatrixProjectionModels.Demographic(),
        mpm, target.n0, target.tspan; p = target.p)
end

end # module
