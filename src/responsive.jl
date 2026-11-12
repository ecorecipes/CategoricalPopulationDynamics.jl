"""
Responsive projection nets and pooled systems.

A `ValuedProjectionNet` holds numbers. In a community, some of those numbers depend on
what the rest of the community is doing: fecundity falls as shared space fills, mortality
rises with the number of parasites. This file adds the three things needed to say that at
the level of named transitions, without writing a simulation loop:

- a [`ResponsiveProjectionNet`](@ref): a valued net whose named transitions carry
  *responses*, functions of a context that scale the transition's values each time step;
- a [`Pool`](@ref): a named total to which components contribute (space occupied, biomass,
  mites per bee) and that responses can read;
- a [`PooledProjectionSystem`](@ref): named components plus the pools that link them.

The system has a definite one-step semantics ([`advance`](@ref)) and lowers to a
`CoupledMPMProblem` in MatrixProjectionModels.jl through `StateDependentMPMTarget`.
"""

# ---------------------------------------------------------------------------
# Stage vectors and contexts
# ---------------------------------------------------------------------------

"""
    StageVector

A stage vector that can be indexed by position or by name. A name may be a stage of the
net, or the name of a stage (or stratum) from which several current stages descend, in
which case the value is their sum: after `expand_stage(net, :pupa, 12)`, `n[:pupa]` is the
total of `pupa1 … pupa12`; after `stratify(net, [:healthy, :infected])`, `n[:larva]` is
the total over both strata, `n[:larva_infected]` is one of them, and `n[:infected]` is
everything in the infected stratum.

This lets a response written for a simple life cycle keep working as the life cycle is
refined.
"""
struct StageVector{V <: AbstractVector{<:Real}} <: AbstractVector{Float64}
    values::V
    groups::Dict{Symbol, Vector{Int}}
end

Base.size(n::StageVector) = size(n.values)
Base.getindex(n::StageVector, i::Int) = Float64(n.values[i])
function Base.getindex(n::StageVector, name::Symbol)
    idx = get(n.groups, name, nothing)
    idx === nothing && throw(KeyError(name))
    total = 0.0
    for i in idx
        total += n.values[i]
    end
    return total
end
Base.haskey(n::StageVector, name::Symbol) = haskey(n.groups, name)

"""
    ResponseContext(n, pool, env)

What a response sees: the component's own stages `n` (a [`StageVector`](@ref)), the totals
of the system's pools `pool` (a `NamedTuple`), and the environment `env` of the time step.
"""
struct ResponseContext{N, P, E}
    n::N
    pool::P
    env::E
end

# ---------------------------------------------------------------------------
# Responsive projection nets
# ---------------------------------------------------------------------------

"""
    ResponsiveProjectionNet(vnet; responses = [], inflows = [], after = [], fecundity = [])

A [`ValuedProjectionNet`](@ref) whose transitions respond to a context.

- `responses`: pairs `transition => f`. Each time step the values of `transition` are
  multiplied by `f(ctx)`, where `ctx` is a [`ResponseContext`](@ref). `f(ctx)` returns a
  number, or a function `(from, to) -> number` to scale entries individually. Several
  responses on one transition multiply.
- `inflows`: pairs `stage => f`; `f(ctx)` individuals are added to `stage` each step,
  whatever the component's own abundance (immigration, or recruitment from a seed rain).
- `after`: functions applied to the new stage vector, in order, after the step (for
  example a quasi-extinction threshold). They should not depend on the number or order of
  stages, so that they survive [`expand_stage`](@ref) and [`stratify`](@ref).
- `fecundity`: names of the transitions that are births, used to split the matrix into
  survival and fecundity parts.

Build one with [`respond`](@ref), [`inflow`](@ref) and [`after_step`](@ref). Responsive
nets combine with `⊕`, and `expand_stage` and `stratify` carry their responses along.
"""
struct ResponsiveProjectionNet
    base::ValuedProjectionNet{Float64}
    responses::Vector{Pair{Symbol, Any}}
    inflows::Vector{Pair{Symbol, Any}}
    after::Vector{Any}
    fecundity::Vector{Symbol}
    groups::Dict{Symbol, Vector{Int}}
    # per transition: name, rows, columns, values, source and target stage names
    compiled::Vector{Tuple{Symbol, Vector{Int}, Vector{Int}, Vector{Float64}, Vector{Symbol}, Vector{Symbol}}}
    by_transition::Dict{Symbol, Vector{Any}}
end

function _float_net(vnet::ValuedProjectionNet)
    vnet isa ValuedProjectionNet{Float64} && return vnet
    return ValuedProjectionNet(vnet.stage_names,
        (t => [(e.first => Float64(e.second)) for e in vnet.transition_values[t]]
         for t in _ordered_transition_names(vnet))...)
end

function ResponsiveProjectionNet(vnet::ValuedProjectionNet;
        responses = Pair{Symbol, Any}[], inflows = Pair{Symbol, Any}[], after = Any[],
        fecundity = Symbol[], groups = nothing)
    base = _float_net(vnet)
    idx = Dict(s => i for (i, s) in enumerate(base.stage_names))
    g = groups === nothing ? Dict{Symbol, Vector{Int}}(s => [i] for (s, i) in idx) : groups
    for s in base.stage_names
        haskey(g, s) || (g[s] = [idx[s]])
    end
    for (t, _) in responses
        haskey(base.transition_values, t) || throw(ArgumentError(
            "response given for unknown transition :$t; transitions are $(_ordered_transition_names(base))"))
    end
    for (s, _) in inflows
        haskey(idx, s) || throw(ArgumentError("inflow into unknown stage :$s"))
    end
    for t in fecundity
        haskey(base.transition_values, t) || throw(ArgumentError("unknown fecundity transition :$t"))
    end
    compiled = map(_ordered_transition_names(base)) do t
        entries = base.transition_values[t]
        (t, [idx[e.first.second] for e in entries], [idx[e.first.first] for e in entries],
         [e.second for e in entries], [e.first.first for e in entries], [e.first.second for e in entries])
    end
    by_transition = Dict{Symbol, Vector{Any}}()
    for (t, f) in responses
        push!(get!(by_transition, t, Any[]), f)
    end
    return ResponsiveProjectionNet(base, Pair{Symbol, Any}[p.first => p.second for p in responses],
        Pair{Symbol, Any}[p.first => p.second for p in inflows], collect(Any, after),
        collect(Symbol, fecundity), g, compiled, by_transition)
end

ResponsiveProjectionNet(net::ResponsiveProjectionNet) = net

_rebuild(net::ResponsiveProjectionNet; base = net.base, responses = net.responses, inflows = net.inflows,
         after = net.after, fecundity = net.fecundity, groups = net.groups) =
    ResponsiveProjectionNet(base; responses, inflows, after, fecundity, groups)

"""
    respond(net, transition => f, ...)

Attach responses to the named transitions of a valued or responsive net; see
[`ResponsiveProjectionNet`](@ref). Returns a responsive net.

```julia
plant = respond(life, :breeding => ctx -> max(0, 1 - ctx.pool.space / 1000))
```
"""
function respond(net, responses::Pair{Symbol}...)
    r = ResponsiveProjectionNet(net)
    return _rebuild(r; responses = vcat(r.responses, Pair{Symbol, Any}[p.first => p.second for p in responses]))
end

"""
    inflow(net, stage => f, ...)

Add `f(ctx)` individuals to `stage` each time step; see [`ResponsiveProjectionNet`](@ref).
"""
function inflow(net, inflows::Pair{Symbol}...)
    r = ResponsiveProjectionNet(net)
    return _rebuild(r; inflows = vcat(r.inflows, Pair{Symbol, Any}[p.first => p.second for p in inflows]))
end

"""
    after_step(net, f)

Apply `f` to the component's new stage vector after each step; see
[`ResponsiveProjectionNet`](@ref).
"""
function after_step(net, f)
    r = ResponsiveProjectionNet(net)
    return _rebuild(r; after = vcat(r.after, Any[f]))
end

"""
    births(net, transition, ...)

Mark transitions as births, so that the matrix can be split into survival and fecundity
parts ([`survival_fecundity_matrices`](@ref)).
"""
function births(net, transitions::Symbol...)
    r = ResponsiveProjectionNet(net)
    return _rebuild(r; fecundity = union(r.fecundity, transitions))
end

stage_names(net::ResponsiveProjectionNet) = stage_names(net.base)
transition_names(net::ResponsiveProjectionNet) = _ordered_transition_names(net.base)
to_matrix(net::ResponsiveProjectionNet) = to_matrix(net.base)

function Base.show(io::IO, net::ResponsiveProjectionNet)
    print(io, "ResponsiveProjectionNet(", length(stage_names(net)), " stages, ",
          length(net.compiled), " transitions, ", length(net.responses), " responses)")
end

"""
    context(net, n, pool, env)

The [`ResponseContext`](@ref) of `net` for stage vector `n`.
"""
context(net::ResponsiveProjectionNet, n::AbstractVector, pool, env) =
    ResponseContext(StageVector(n, net.groups), pool, env)

_factor(m::Number, from, to) = m
_factor(m, from, to) = m(from, to)

function _fill_matrix!(A, net::ResponsiveProjectionNet, ctx, keep)
    for (t, rows, cols, vals, froms, tos) in net.compiled
        keep(t) || continue
        fs = get(net.by_transition, t, nothing)
        if fs === nothing
            for k in eachindex(vals)
                A[rows[k], cols[k]] += vals[k]
            end
        else
            ms = [f(ctx) for f in fs]
            for k in eachindex(vals)
                v = vals[k]
                for m in ms
                    v *= _factor(m, froms[k], tos[k])
                end
                A[rows[k], cols[k]] += v
            end
        end
    end
    return A
end

"""
    to_matrix(net::ResponsiveProjectionNet, ctx)

The projection matrix of `net` with its responses evaluated at `ctx`.
"""
function to_matrix(net::ResponsiveProjectionNet, ctx::ResponseContext)
    k = length(stage_names(net))
    return _fill_matrix!(zeros(Float64, k, k), net, ctx, t -> true)
end

"""
    survival_fecundity_matrices(net::ResponsiveProjectionNet, ctx)

`(U, F)`: the matrices of the transitions not marked, and marked, as [`births`](@ref),
with responses evaluated at `ctx`.
"""
function survival_fecundity_matrices(net::ResponsiveProjectionNet, ctx::ResponseContext)
    k = length(stage_names(net))
    U = _fill_matrix!(zeros(Float64, k, k), net, ctx, t -> !(t in net.fecundity))
    F = _fill_matrix!(zeros(Float64, k, k), net, ctx, t -> t in net.fecundity)
    return U, F
end

"""
    evaluate(net::ResponsiveProjectionNet, ctx)

The plain [`ValuedProjectionNet`](@ref) obtained by evaluating the responses of `net` at
`ctx`: the model frozen at one moment, with every value still attached to its named
transition.
"""
function evaluate(net::ResponsiveProjectionNet, ctx::ResponseContext)
    result = net.base
    for (t, fs) in net.by_transition
        ms = [f(ctx) for f in fs]
        result = map_values(result, t) do (from, to), val
            for m in ms
                val *= _factor(m, from, to)
            end
            val
        end
    end
    return result
end

function _merge_two(a::ResponsiveProjectionNet, b::ResponsiveProjectionNet)
    base = _merge_two(a.base, b.base)
    groups = merge(a.groups, b.groups)
    return ResponsiveProjectionNet(base; responses = vcat(a.responses, b.responses),
        inflows = vcat(a.inflows, b.inflows), after = vcat(a.after, b.after),
        fecundity = union(a.fecundity, b.fecundity), groups = groups)
end
_merge_two(a::ResponsiveProjectionNet, b::ValuedProjectionNet) = _merge_two(a, ResponsiveProjectionNet(b))
_merge_two(a::ValuedProjectionNet, b::ResponsiveProjectionNet) = _merge_two(ResponsiveProjectionNet(a), b)

const _AnyNet = Union{ValuedProjectionNet, ResponsiveProjectionNet}
⊕(a::ResponsiveProjectionNet, b::_AnyNet) = _merge_two(a, b)
⊕(a::ValuedProjectionNet, b::ResponsiveProjectionNet) = _merge_two(a, b)
Base.merge(a::ResponsiveProjectionNet, b::_AnyNet, rest::_AnyNet...) = foldl(_merge_two, rest; init = _merge_two(a, b))
Base.merge(a::ValuedProjectionNet, b::ResponsiveProjectionNet, rest::_AnyNet...) =
    foldl(_merge_two, rest; init = _merge_two(a, b))

function expand_stage(net::ResponsiveProjectionNet, stage::Symbol, n::Integer;
        ageing = 1.0, name::Symbol = Symbol(stage, :_ageing))
    old = stage_names(net)
    base = expand_stage(net.base, stage, n; ageing, name)
    position = Dict(s => i for (i, s) in enumerate(stage_names(base)))
    classes = [position[Symbol(stage, i)] for i in 1:n]
    remap(i) = old[i] === stage ? classes : [position[old[i]]]
    groups = Dict{Symbol, Vector{Int}}(g => reduce(vcat, [remap(i) for i in idx]; init = Int[])
                                       for (g, idx) in net.groups)
    inflows = Pair{Symbol, Any}[(s === stage ? Symbol(stage, 1) : s) => f for (s, f) in net.inflows]
    return ResponsiveProjectionNet(base; responses = net.responses, inflows, after = net.after,
        fecundity = net.fecundity, groups)
end

function expand_stages(net::ResponsiveProjectionNet, durations::Pair{Symbol, <:Integer}...;
        ageing::AbstractDict = Dict{Symbol, Any}())
    result = net
    for (stage, n) in durations
        result = expand_stage(result, stage, n; ageing = get(ageing, stage, 1.0))
    end
    return result
end

function stratify(net::ResponsiveProjectionNet, strata::AbstractVector{Symbol};
        coupling::AbstractDict = Dict{Symbol, Any}(), sep = "_")
    base = stratify(net.base, strata; coupling, sep)
    m = length(stage_names(net))
    derived = Set(_ordered_transition_names(base))
    # a response on a transition applies to every transition derived from it
    names_from(t) = [stratum_transition(t, kf, kt; sep) for kf in strata for kt in strata
                     if stratum_transition(t, kf, kt; sep) in derived]
    responses = Pair{Symbol, Any}[d => f for (t, f) in net.responses for d in names_from(t)]
    fecundity = Symbol[d for t in net.fecundity for d in names_from(t)]
    groups = Dict{Symbol, Vector{Int}}()
    for (g, idx) in net.groups
        groups[g] = [(j - 1) * m + i for j in eachindex(strata) for i in idx]
        for (j, stratum) in enumerate(strata)
            groups[stratum_stage(g, stratum; sep)] = [(j - 1) * m + i for i in idx]
        end
    end
    for (j, stratum) in enumerate(strata)
        haskey(groups, stratum) || (groups[stratum] = collect(((j - 1) * m + 1):(j * m)))
    end
    # inflows enter the first stratum
    inflows = Pair{Symbol, Any}[stratum_stage(s, first(strata); sep) => f for (s, f) in net.inflows]
    return ResponsiveProjectionNet(base; responses, inflows, after = net.after, fecundity, groups)
end

# ---------------------------------------------------------------------------
# Pools and pooled systems
# ---------------------------------------------------------------------------

"""
    Pool(name, component => contribution, ...)

A named total shared by the components of a [`PooledProjectionSystem`](@ref). Each listed
component contributes

- `weights::Vector` (one per stage): the weighted sum of its stages;
- `[stage => weight, ...]`: the weighted sum of the named stages (names may be groups, as
  in [`StageVector`](@ref));
- a number `w`: `w` times the component's total;
- a function `(n, env) -> number` of its [`StageVector`](@ref) and the environment.

The pool's value is the sum of the contributions, in the order given.

```julia
Pool(:space, :grass => [:adult => 1.0], :shrub => [:juvenile => 1.0, :adult => 4.0])
```
"""
struct Pool
    name::Symbol
    contributions::Vector{Pair{Symbol, Any}}
end
Pool(name::Symbol, contributions::Pair{Symbol}...) =
    Pool(name, Pair{Symbol, Any}[c.first => c.second for c in contributions])

_contribution(w::Number, n::StageVector, env) = w * sum(n.values)
_contribution(w::AbstractVector{<:Number}, n::StageVector, env) = dot(w, n.values)
function _contribution(w::AbstractVector{<:Pair}, n::StageVector, env)
    total = 0.0
    for (stage, weight) in w
        total += weight * n[stage]
    end
    return total
end
_contribution(f, n::StageVector, env) = f(n, env)

"""
    PooledProjectionSystem(name => net, ...; pools = [])

Named components (valued or responsive projection nets) linked by [`Pool`](@ref)s. This is
a community: each component's responses can read every pool, and each pool sums what the
listed components contribute. No component refers to another directly.

One time step is defined by [`advance`](@ref); [`trajectory`](@ref) iterates it. With
MatrixProjectionModels.jl loaded, `lower(system, StateDependentMPMTarget(n0, tspan; p =
environments))` gives a `CoupledMPMProblem` with the same dynamics.
"""
struct PooledProjectionSystem
    order::Vector{Symbol}
    components::Dict{Symbol, ResponsiveProjectionNet}
    pools::Vector{Pool}
end

function PooledProjectionSystem(pairs::Pair{Symbol}...; pools = Pool[])
    isempty(pairs) && throw(ArgumentError("PooledProjectionSystem must have at least one component"))
    order = Symbol[]
    components = Dict{Symbol, ResponsiveProjectionNet}()
    for (name, net) in pairs
        name in order && throw(ArgumentError("duplicate component name: $name"))
        push!(order, name)
        components[name] = ResponsiveProjectionNet(net)
    end
    pool_names = Symbol[]
    for pool in pools
        pool.name in pool_names && throw(ArgumentError("duplicate pool name: $(pool.name)"))
        push!(pool_names, pool.name)
        for (component, w) in pool.contributions
            haskey(components, component) ||
                throw(ArgumentError("pool :$(pool.name) lists unknown component :$component"))
            w isa AbstractVector{<:Number} && length(w) != length(stage_names(components[component])) &&
                throw(DimensionMismatch("pool :$(pool.name) needs one weight per stage of :$component"))
        end
    end
    return PooledProjectionSystem(order, components, collect(Pool, pools))
end

Base.getindex(sys::PooledProjectionSystem, name::Symbol) = sys.components[name]
Base.haskey(sys::PooledProjectionSystem, name::Symbol) = haskey(sys.components, name)
Base.length(sys::PooledProjectionSystem) = length(sys.order)
component_names(sys::PooledProjectionSystem) = sys.order
stage_names(sys::PooledProjectionSystem, name::Symbol) = stage_names(sys[name])

"""
    pool_names(sys)

Names of the pools of a [`PooledProjectionSystem`](@ref).
"""
pool_names(sys::PooledProjectionSystem) = Symbol[p.name for p in sys.pools]

function Base.show(io::IO, sys::PooledProjectionSystem)
    print(io, "PooledProjectionSystem(", join(sys.order, ", "), "; pools = ", join(pool_names(sys), ", "), ")")
end

"""
    pool_totals(sys, state, env)

The value of every pool of `sys`, as a `NamedTuple`, for `state` (a dictionary from
component name to stage vector) and environment `env`.
"""
function pool_totals(sys::PooledProjectionSystem, state::AbstractDict, env)
    values = map(sys.pools) do pool
        total = 0.0
        for (component, w) in pool.contributions
            total += _contribution(w, StageVector(state[component], sys[component].groups), env)
        end
        total
    end
    return NamedTuple{Tuple(pool_names(sys))}(Tuple(values))
end

function _inflows(net::ResponsiveProjectionNet, ctx)
    added = zeros(Float64, length(stage_names(net)))
    for (stage, f) in net.inflows
        added[only(net.groups[stage])] += f(ctx)
    end
    return added
end

function _after(net::ResponsiveProjectionNet, n::AbstractVector)
    for f in net.after
        n = f(n)
    end
    return n
end

"""
    advance(sys, state, env)

One time step of a [`PooledProjectionSystem`](@ref). The pools are computed from `state`;
every component's matrix is evaluated at its own stages, those pools and `env`, and
applied; inflows are added; after-step maps are applied. All components are updated from
the same state. Returns the new state.
"""
function advance(sys::PooledProjectionSystem, state::AbstractDict, env)
    pool = pool_totals(sys, state, env)
    next = Dict{Symbol, Vector{Float64}}()
    for name in sys.order
        net = sys[name]
        n = state[name]
        ctx = context(net, n, pool, env)
        stepped = to_matrix(net, ctx) * n
        isempty(net.inflows) || (stepped = stepped .+ _inflows(net, ctx))
        next[name] = collect(Float64, _after(net, stepped))
    end
    return next
end

"""
    trajectory(sys, state, envs)

Iterate [`advance`](@ref) through the environments `envs`. Returns `(states, pools)`: the
state at each time (one more than `length(envs)`) and the pool totals used for each step.
"""
function trajectory(sys::PooledProjectionSystem, state::AbstractDict, envs)
    current = Dict{Symbol, Vector{Float64}}(name => collect(Float64, state[name]) for name in sys.order)
    states = [current]
    pools = Any[]
    for env in envs
        push!(pools, pool_totals(sys, current, env))
        current = advance(sys, current, env)
        push!(states, current)
    end
    return (states = states, pools = pools)
end
