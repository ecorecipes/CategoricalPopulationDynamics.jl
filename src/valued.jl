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

# ---------------------------------------------------------------------------
# merge: compose ValuedProjectionNets from smaller pieces
# ---------------------------------------------------------------------------

"""
    merge(a::ValuedProjectionNet, b::ValuedProjectionNet)

Combine two `ValuedProjectionNet`s that share the **same stage names** (same order)
but have **disjoint transition names** into a single net containing all transitions.

This lets you build complex models from small, readable pieces:

```julia
surv = ValuedProjectionNet([:egg, :larva, :adult],
    :survival => [(:egg => :larva) => 0.5, (:larva => :adult) => 0.3])
fec  = ValuedProjectionNet([:egg, :larva, :adult],
    :fecundity => [(:adult => :egg) => 10.0])
full = merge(surv, fec)          # contains both :survival and :fecundity
to_matrix(full) == to_matrix(surv) + to_matrix(fec)  # true
```

Errors if the stage names differ or if any transition name appears in both nets.
Supports variadic calls: `merge(a, b, c, ...)`.
"""
function _merge_two(a::ValuedProjectionNet{Ta}, b::ValuedProjectionNet{Tb}) where {Ta, Tb}
    a.stage_names == b.stage_names || throw(ArgumentError(
        "Cannot merge ValuedProjectionNets with different stage names: " *
        "$(a.stage_names) vs $(b.stage_names)"))

    overlap = intersect(keys(a.transition_values), keys(b.transition_values))
    isempty(overlap) || throw(ArgumentError(
        "Transition names overlap: $(collect(overlap)). " *
        "Use distinct names or map_values to modify existing transitions."))

    T = promote_type(Ta, Tb)

    merged_tv = Dict{Symbol, Vector{Pair{Pair{Symbol,Symbol}, T}}}()
    for (k, v) in a.transition_values
        merged_tv[k] = [((e.first.first => e.first.second) => T(e.second)) for e in v]
    end
    for (k, v) in b.transition_values
        merged_tv[k] = [((e.first.first => e.first.second) => T(e.second)) for e in v]
    end

    all_tnames = collect(keys(merged_tv))
    net = LabelledProjectionNet([:stage],
        (tn => (:stage => :stage) for tn in all_tnames)...)

    return ValuedProjectionNet{T}(net, copy(a.stage_names), merged_tv)
end

function Base.merge(a::ValuedProjectionNet{Ta}, b::ValuedProjectionNet{Tb}) where {Ta, Tb}
    _merge_two(a, b)
end

function Base.merge(a::ValuedProjectionNet, b::ValuedProjectionNet,
        rest::ValuedProjectionNet...)
    return foldl(_merge_two, rest; init=_merge_two(a, b))
end

# ---------------------------------------------------------------------------
# map_values: transform transition entries selectively
# ---------------------------------------------------------------------------

"""
    map_values(f, vnet::ValuedProjectionNet, tname::Symbol)

Return a new `ValuedProjectionNet` where every entry `(from => to) => val`
in transition `tname` is replaced by `(from => to) => f((from, to), val)`.
All other transitions are unchanged.

Useful for applying genotype- or environment-specific modifiers without
rebuilding the whole net:

```julia
# Reduce larval survival by Bt mortality factor
vnet_bt = map_values(bollworm, :survival) do (from, to), val
    from == :larva ? val * (1 - μ_bt) : val
end
```
"""
function map_values(f, vnet::ValuedProjectionNet{T}, tname::Symbol) where {T}
    haskey(vnet.transition_values, tname) ||
        throw(ArgumentError("Unknown transition :$tname"))

    entries = vnet.transition_values[tname]
    new_entries = [(e.first => f(e.first, e.second)) for e in entries]

    # Determine new element type
    new_vals = [e.second for e in new_entries]
    S = isempty(new_vals) ? T : promote_type(T, map(typeof, new_vals)...)
    S = S <: AbstractFloat ? S : Float64

    new_tv = Dict{Symbol, Vector{Pair{Pair{Symbol,Symbol}, S}}}()
    for (k, v) in vnet.transition_values
        if k == tname
            new_tv[k] = [((e.first.first => e.first.second) => S(e.second)) for e in new_entries]
        else
            new_tv[k] = [((e.first.first => e.first.second) => S(e.second)) for e in v]
        end
    end

    return ValuedProjectionNet{S}(vnet.net, copy(vnet.stage_names), new_tv)
end

"""
    map_values(f, vnet::ValuedProjectionNet)

Apply `f((from, to), val)` to **all** transitions. Returns a new net.

```julia
# Scale all transition values by 0.9
scaled = map_values(bollworm) do _, val
    0.9 * val
end
```
"""
function map_values(f, vnet::ValuedProjectionNet{T}) where {T}
    result = vnet
    for tname in keys(vnet.transition_values)
        result = map_values(f, result, tname)
    end
    return result
end

# ---------------------------------------------------------------------------
# Unicode operators
# ---------------------------------------------------------------------------

"""
    a ⊕ b

Direct sum (merge) of two `ValuedProjectionNet`s. Equivalent to `merge(a, b)`.

Type `\\oplus<TAB>` in the Julia REPL or a supporting editor.

```julia
full = survival_net ⊕ fecundity_net          # two pieces
full = survival_net ⊕ fecundity_net ⊕ aging   # left-associative chain
```
"""
⊕(a::ValuedProjectionNet, b::ValuedProjectionNet) = _merge_two(a, b)

"""
    vnet ⊘ (:transition_name => f)

Apply `map_values(f, vnet, :transition_name)`. Equivalent to:

```julia
map_values(f, vnet, :transition_name)
```

Type `\\oslash<TAB>` in the Julia REPL or a supporting editor.

```julia
# Halve larval survival
vnet_bt = bollworm ⊘ (:survival => ((from, _), val) -> from == :larva ? val * 0.5 : val)
```

For complex transformations, prefer the `map_values` do-block form instead.
"""
⊘(vnet::ValuedProjectionNet, p::Pair{Symbol, <:Function}) = map_values(p.second, vnet, p.first)
