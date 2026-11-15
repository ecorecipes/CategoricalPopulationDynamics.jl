"""
Stage structure of valued projection nets: giving a stage a fixed duration, and
replicating a net across strata.

Both operations act on named nets and return named nets, so models built from them stay
readable: `expand_stage` turns `:pupa` into `:pupa1 … :pupa12`, and `stratify` turns
`:larva` into `:larva_healthy` and `:larva_infected`.
"""

"""
    expand_stage(vnet, stage, n; ageing = 1.0, name = Symbol(stage, :_ageing))

Give `stage` a fixed duration of `n` time steps by replacing it with the age classes
`stage1, …, stagen`. `n` must be at least 2.

Transitions into `stage` now enter `stage1`; transitions out of `stage` now leave
`stagen`. A new transition called `name` moves individuals from each class to the next,
with value `ageing` (a number, or a vector of `n - 1` values, one per step). A transition
from `stage` to itself has no meaning once the stage has a fixed duration and is an error.

```julia
life = ValuedProjectionNet([:egg, :adult],
    :hatching => [(:egg => :adult) => 0.5],
    :laying   => [(:adult => :egg) => 10.0])
daily = expand_stage(life, :egg, 3; ageing = 0.9)
stage_names(daily)            # [:egg1, :egg2, :egg3, :adult]
```
"""
function expand_stage(vnet::ValuedProjectionNet{T}, stage::Symbol, n::Integer;
        ageing = one(T), name::Symbol = Symbol(stage, :_ageing)) where {T}
    stage in vnet.stage_names || throw(ArgumentError("Unknown stage :$stage"))
    n >= 2 || throw(ArgumentError("a stage needs at least two age classes to be expanded, got $n"))
    haskey(vnet.transition_values, name) &&
        throw(ArgumentError("transition :$name already exists; pass another `name`"))
    steps = ageing isa AbstractVector ? collect(ageing) : fill(ageing, n - 1)
    length(steps) == n - 1 ||
        throw(DimensionMismatch("`ageing` needs $(n - 1) values for $n age classes, got $(length(steps))"))

    classes = [Symbol(stage, i) for i in 1:n]
    isempty(intersect(classes, vnet.stage_names)) ||
        throw(ArgumentError("age classes $(classes) clash with existing stage names"))
    new_stages = Symbol[]
    for s in vnet.stage_names
        s === stage ? append!(new_stages, classes) : push!(new_stages, s)
    end

    transitions = Pair{Symbol, Vector{Pair{Pair{Symbol, Symbol}, Float64}}}[]
    for tname_val in _ordered_transition_names(vnet)
        entries = Pair{Pair{Symbol, Symbol}, Float64}[]
        for ((from, to), val) in vnet.transition_values[tname_val]
            (from === stage && to === stage) && throw(ArgumentError(
                "transition :$tname_val keeps individuals in :$stage, which cannot be given a fixed duration"))
            push!(entries, ((from === stage ? classes[end] : from) => (to === stage ? classes[1] : to)) => val)
        end
        push!(transitions, tname_val => entries)
    end
    push!(transitions, name => [(classes[i] => classes[i + 1]) => Float64(steps[i]) for i in 1:(n - 1)])
    return ValuedProjectionNet(new_stages, transitions...)
end

"""
    expand_stages(vnet, stage => n, ...; ageing = Dict())

Apply [`expand_stage`](@ref) to several stages. `ageing` maps a stage to its ageing value
(default 1.0).
"""
function expand_stages(vnet::ValuedProjectionNet, durations::Pair{Symbol, <:Integer}...;
        ageing::AbstractDict = Dict{Symbol, Any}())
    result = vnet
    for (stage, n) in durations
        result = expand_stage(result, stage, n; ageing = get(ageing, stage, 1.0))
    end
    return result
end

# Transition names in a reproducible order (the underlying storage is a Dict).
_ordered_transition_names(vnet::ValuedProjectionNet) = sort!(collect(keys(vnet.transition_values)))

"""
    stratum_stage(stage, stratum; sep = "_")

The name [`stratify`](@ref) gives to `stage` in `stratum`, for example
`stratum_stage(:larva, :infected) == :larva_infected`.
"""
stratum_stage(stage::Symbol, stratum::Symbol; sep = "_") = Symbol(stage, sep, stratum)

"""
    stratum_transition(transition, from[, to]; sep = "_")

The name [`stratify`](@ref) gives to `transition` within stratum `from`
(`:ageing_infected`), or from stratum `from` to stratum `to`
(`:capping_healthy_to_infected`).
"""
stratum_transition(t::Symbol, from::Symbol; sep = "_") = Symbol(t, sep, from)
stratum_transition(t::Symbol, from::Symbol, to::Symbol; sep = "_") =
    from === to ? stratum_transition(t, from; sep) : Symbol(t, sep, from, :_to_, to)

"""
    stratify(vnet::ValuedProjectionNet, strata; coupling = Dict(), sep = "_")

Replicate a valued projection net across `strata` (for example infection states, or
patches), keeping names.

Every stage `s` becomes `s_k` for each stratum `k`, stratum by stratum, and every
transition `t` becomes `t_k` acting within stratum `k`. `coupling` maps a transition name
to a square matrix `C` over the strata: where `C[to, from]` is non-zero for two different
strata, a transition `t_from_to_to` is added that moves individuals between them, and all
values are multiplied by the corresponding entry of `C`. Transitions without an entry in
`coupling` stay within their stratum.

```julia
life = ValuedProjectionNet([:juvenile, :adult],
    :maturing => [(:juvenile => :adult) => 0.3],
    :breeding => [(:adult => :juvenile) => 2.0])
# two patches; a tenth of the young settle in the other patch
two = stratify(life, [:north, :south]; coupling = Dict(:breeding => [0.9 0.1; 0.1 0.9]))
sort(transition_names(two))
# [:breeding_north, :breeding_north_to_south, :breeding_south, :breeding_south_to_north,
#  :maturing_north, :maturing_south]
```

The matrix of the result equals the sum over transitions of the matrix form
`stratify(transition_matrix(vnet, t), C)`, so the two levels agree.
"""
function stratify(vnet::ValuedProjectionNet, strata::AbstractVector{Symbol};
        coupling::AbstractDict = Dict{Symbol, Any}(), sep = "_")
    allunique(strata) || throw(ArgumentError("strata must be distinct, got $(strata)"))
    isempty(strata) && throw(ArgumentError("at least one stratum is needed"))
    k = length(strata)
    for (t, C) in coupling
        haskey(vnet.transition_values, t) || throw(ArgumentError("coupling given for unknown transition :$t"))
        size(C) == (k, k) || throw(DimensionMismatch("coupling for :$t must be $(k)×$(k), got $(size(C))"))
    end
    new_stages = [stratum_stage(s, stratum; sep) for stratum in strata for s in vnet.stage_names]
    transitions = Pair{Symbol, Vector{Pair{Pair{Symbol, Symbol}, Float64}}}[]
    for t in _ordered_transition_names(vnet)
        C = get(coupling, t, nothing)
        for (jf, kf) in enumerate(strata), (jt, kt) in enumerate(strata)
            weight = C === nothing ? (jf == jt ? 1.0 : 0.0) : Float64(C[jt, jf])
            weight == 0 && continue
            entries = [(stratum_stage(from, kf; sep) => stratum_stage(to, kt; sep)) => weight * val
                       for ((from, to), val) in vnet.transition_values[t]]
            push!(transitions, stratum_transition(t, kf, kt; sep) => entries)
        end
    end
    return ValuedProjectionNet(new_stages, transitions...)
end
