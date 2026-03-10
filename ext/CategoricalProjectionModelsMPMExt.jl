module CategoricalProjectionModelsMPMExt

using CategoricalProjectionModels
using MatrixProjectionModels

"""
    lower(net, target::MPMTarget, transition_data)

Lower a LabelledProjectionNet to a MatrixProjectionModel.

`transition_data` is a Dict{Symbol, Matrix} mapping transition names to
sub-matrices. The full projection matrix is their additive sum.
"""
function CategoricalProjectionModels.lower(
        net::CategoricalProjectionModels.LabelledProjectionNet,
        target::MPMTarget,
        transition_data::Dict{Symbol, <:AbstractMatrix})
    tnames = CategoricalProjectionModels.tname(net)
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
function CategoricalProjectionModels.lift(
        mpm::MatrixProjectionModels.MatrixProjectionModel,
        target::ProjectionNetTarget)
    # Create a net with one aggregate state and one transition
    # (sub-transition decomposition is not recoverable from the aggregated matrix)
    net = CategoricalProjectionModels.LabelledProjectionNet(
        [:population],
        :projection => (:population => :population))
    return net
end

"""
    lower(vnet::ValuedProjectionNet, target::MPMTarget)

Lower a ValuedProjectionNet directly to a MatrixProjectionModel.
The full projection matrix is the additive sum of all transition matrices.
"""
function CategoricalProjectionModels.lower(
        vnet::CategoricalProjectionModels.ValuedProjectionNet,
        target::MPMTarget)
    A = CategoricalProjectionModels.to_matrix(vnet)
    snames = CategoricalProjectionModels.stage_names(vnet)
    return MatrixProjectionModels.MatrixProjectionModel(A; stage_names=snames)
end

"""
    lower(net::LabelledProjectionNet, target::MPMTarget, transition_data, stage_names)

Lower a LabelledProjectionNet with sparse transition data to a MatrixProjectionModel.

`transition_data` is a `Dict{Symbol, Vector{Pair{Pair{Symbol,Symbol}, <:Real}}}`.
`stage_names` is a `Vector{Symbol}` of ordered stage labels.
"""
function CategoricalProjectionModels.lower(
        net::CategoricalProjectionModels.LabelledProjectionNet,
        target::MPMTarget,
        transition_data::Dict{Symbol, <:AbstractVector{<:Pair}},
        stage_names::Vector{Symbol})
    vnet = CategoricalProjectionModels.ValuedProjectionNet(stage_names,
        (tn => transition_data[tn] for tn in keys(transition_data))...)
    return CategoricalProjectionModels.lower(vnet, target)
end

end # module
