"""
Valued projection nets: LabelledProjectionNet + stage names + sparse transition values.

Follows the AlgebraicPetri `LabelledReactionNet` pattern — bundles categorical
structure with numeric data.

# Example
```julia
vnet = ValuedProjectionNet([:seed, :small, :large],
    :survival => [(:seed => :small) => 0.2, (:small => :large) => 0.4,
                  (:small => :small) => 0.3, (:large => :large) => 0.7],
    :fecundity => [(:large => :seed) => 5.0, (:small => :seed) => 1.0])
```
"""

"""
    ValuedProjectionNet{T<:Real}

A projection net with named stages and sparse numeric values per transition.

# Fields
- `net::LabelledProjectionNet`: Categorical topology (single state `:stage`, transitions as processes)
- `stage_names::Vector{Symbol}`: Ordered stage/bin labels
- `transition_values::Dict{Symbol, Vector{Pair{Pair{Symbol,Symbol}, T}}}`: Sparse entries per transition
"""
struct ValuedProjectionNet{T<:Real}
    net::LabelledProjectionNet
    stage_names::Vector{Symbol}
    transition_values::Dict{Symbol, Vector{Pair{Pair{Symbol,Symbol}, T}}}
end

"""
    ValuedProjectionNet(stage_names, transitions...)

Construct a `ValuedProjectionNet` from named stages and transition specifications.

Each transition is `name => [(from => to) => value, ...]`.

# Example
```julia
vnet = ValuedProjectionNet([:seed, :small, :large],
    :survival => [(:seed => :small) => 0.2, (:large => :large) => 0.7],
    :fecundity => [(:large => :seed) => 5.0])
```
"""
function ValuedProjectionNet(stage_names::AbstractVector{Symbol},
        transitions::Pair{Symbol, <:AbstractVector{<:Pair{Pair{Symbol,Symbol}, <:Real}}}...)
    stage_set = Set(stage_names)

    # Validate all stage references and determine element type
    all_vals = Real[]
    for (tname_val, entries) in transitions
        for ((from, to), val) in entries
            from in stage_set || throw(ArgumentError("Unknown stage name :$from in transition :$tname_val"))
            to in stage_set || throw(ArgumentError("Unknown stage name :$to in transition :$tname_val"))
            push!(all_vals, val)
        end
    end

    T = isempty(all_vals) ? Float64 : promote_type(map(typeof, all_vals)...)
    T = T <: AbstractFloat ? T : Float64

    # Build the LabelledProjectionNet with a single state :stage
    tnames = Symbol[t.first for t in transitions]
    net = LabelledProjectionNet([:stage],
        (tn => (:stage => :stage) for tn in tnames)...)

    # Store transition values with promoted type
    tv = Dict{Symbol, Vector{Pair{Pair{Symbol,Symbol}, T}}}()
    for (tname_val, entries) in transitions
        tv[tname_val] = [((from => to) => T(val)) for ((from, to), val) in entries]
    end

    return ValuedProjectionNet{T}(net, collect(Symbol, stage_names), tv)
end

"""
    stage_names(vnet::ValuedProjectionNet)

Return the ordered stage names.
"""
stage_names(vnet::ValuedProjectionNet) = vnet.stage_names

"""
    transition_names(vnet::ValuedProjectionNet)

Return the transition names.
"""
transition_names(vnet::ValuedProjectionNet) = collect(keys(vnet.transition_values))

"""
    transition_matrix(vnet::ValuedProjectionNet, tname::Symbol)

Materialize a single transition's sparse entries to a dense matrix.
Convention: `(from => to) => value` sets `M[to_idx, from_idx] = value`.
"""
function transition_matrix(vnet::ValuedProjectionNet{T}, tname_val::Symbol) where {T}
    haskey(vnet.transition_values, tname_val) ||
        throw(ArgumentError("Unknown transition :$tname_val"))
    n = length(vnet.stage_names)
    stage_idx = Dict(s => i for (i, s) in enumerate(vnet.stage_names))
    M = zeros(T, n, n)
    for ((from, to), val) in vnet.transition_values[tname_val]
        M[stage_idx[to], stage_idx[from]] += val
    end
    return M
end

"""
    to_matrix(vnet::ValuedProjectionNet)

Materialize the sum of all transition matrices.
"""
function to_matrix(vnet::ValuedProjectionNet{T}) where {T}
    n = length(vnet.stage_names)
    A = zeros(T, n, n)
    for tname_val in keys(vnet.transition_values)
        A .+= transition_matrix(vnet, tname_val)
    end
    return A
end
