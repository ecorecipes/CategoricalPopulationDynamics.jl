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
`CoupledMPMProblem` in MatrixProjectionModels.jl through `StateDependentMPMTarget`, or to a
`CoupledIPMProblem` in IntegralProjectionModels.jl through `CoupledIPMTarget`.
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
  multiplied by `f(ctx)`, where `ctx` is a [`ResponseContext`](@ref). `f(ctx)` returns
  - a number, which scales every entry of the transition;
  - a matrix `M` with one row and one column per stage, laid out like `to_matrix(net)`:
    the entry from stage `j` to stage `i` is multiplied by `M[i, j]`;
  - a function `(from, to) -> number` of the stage names, called for each entry.

  Several responses on one transition multiply.
- `inflows`: pairs `stage => f`; `f(ctx)` individuals are added to `stage` each step,
  whatever the component's own abundance (immigration, or recruitment from a seed rain).
- `after`: functions applied to the new stage vector, in order, after the step (for
  example a quasi-extinction threshold). They should not depend on the number or order of
  stages, so that they survive [`expand_stage`](@ref) and [`stratify`](@ref).
- `fecundity`: names of the transitions that are births, used to split the matrix into
  survival and fecundity parts.
- `meshes`: the stages that are mesh cells of a continuous trait, as a list of
  `(name = mesh, domain = ContinuousDomain(lower, upper, cells), cells = [stage, ...])`, the
  cells in the order of their mesh points. This is metadata: it does not change the net's
  matrices, and tells a lowering such as `CoupledIPMTarget` which stages form a continuous
  state. See [`meshes`](@ref).

Build one with [`respond`](@ref), [`inflow`](@ref) and [`after_step`](@ref). Responsive
nets combine with `⊕`, and `expand_stage` and `stratify` carry their responses (and meshes)
along.

A matrix is the cheap way to scale many entries individually, for example a transition
among the cells of a discretised trait. Any `AbstractMatrix` will do, and its values where
the transition has no entry are ignored: a response scales a transition, it does not add
to it.

A matrix or a function of stage names refers to the stages the net has when the response
is attached. After `expand_stage` or `stratify` neither needs to change: every entry of
the refined net takes the factor of the entry it derives from, so a function is still
called with the names it was written for (`:egg`, not `:egg3` or `:egg_infected`). A
response attached after the refinement sees the refined stages.
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
    meshes::Vector{NamedTuple{(:name, :domain, :cells), Tuple{Symbol, ContinuousDomain{Float64}, Vector{Symbol}}}}
end

const _Mesh = NamedTuple{(:name, :domain, :cells), Tuple{Symbol, ContinuousDomain{Float64}, Vector{Symbol}}}

function _mesh(m, stages::AbstractVector{Symbol})
    name, domain, cells = m isa NamedTuple ? (m.name, m.domain, m.cells) : (m[1], m[2], m[3])
    d = ContinuousDomain(Float64(domain.lower), Float64(domain.upper), domain.n_meshpoints)
    cells = collect(Symbol, cells)
    length(cells) == d.n_meshpoints || throw(ArgumentError(
        "mesh :$name has $(d.n_meshpoints) mesh points but $(length(cells)) cells"))
    for c in cells
        c in stages || throw(ArgumentError("cell :$c of mesh :$name is not a stage of the net"))
    end
    return _Mesh((Symbol(name), d, cells))
end

function _float_net(vnet::ValuedProjectionNet)
    vnet isa ValuedProjectionNet{Float64} && return vnet
    return ValuedProjectionNet(vnet.stage_names,
        (t => [(e.first => Float64(e.second)) for e in vnet.transition_values[t]]
         for t in _ordered_transition_names(vnet))...)
end

function ResponsiveProjectionNet(vnet::ValuedProjectionNet;
        responses = Pair{Symbol, Any}[], inflows = Pair{Symbol, Any}[], after = Any[],
        fecundity = Symbol[], groups = nothing, meshes = _Mesh[])
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
    mesh_list = _Mesh[_mesh(m, base.stage_names) for m in meshes]
    allunique(m.name for m in mesh_list) || throw(ArgumentError("mesh names must be unique"))
    return ResponsiveProjectionNet(base, Pair{Symbol, Any}[p.first => p.second for p in responses],
        Pair{Symbol, Any}[p.first => p.second for p in inflows], collect(Any, after),
        collect(Symbol, fecundity), g, compiled, by_transition, mesh_list)
end

ResponsiveProjectionNet(net::ResponsiveProjectionNet) = net

_rebuild(net::ResponsiveProjectionNet; base = net.base, responses = net.responses, inflows = net.inflows,
         after = net.after, fecundity = net.fecundity, groups = net.groups, meshes = net.meshes) =
    ResponsiveProjectionNet(base; responses, inflows, after, fecundity, groups, meshes)

"""
    meshes(net)

The meshes of a responsive net: the stages that are the cells of a continuous trait, as a
vector of `(name, domain, cells)` named tuples (see [`ResponsiveProjectionNet`](@ref)). Empty
for a net without them, and for a `ValuedProjectionNet`. They are carried through `respond`,
`births`, `inflow`, `after_step`, `⊕`, [`expand_stage`](@ref) (a mesh one of whose cells is
expanded is dropped, since its cells are no longer one stage each) and [`stratify`](@ref)
(each mesh is copied into every stratum, named as the stages are: `stratum_stage(name,
stratum)`).
"""
meshes(net::ResponsiveProjectionNet) = net.meshes
meshes(net::ValuedProjectionNet) = _Mesh[]

"""
    state_layout(net)

The stages of `net` as the states of an integral projection model, in stage order: a
`NamedTuple` whose entries are a `ContinuousDomain` for each mesh (see [`meshes`](@ref))
whose cells are consecutive stages, under the mesh's name, and a `DiscreteDomain` with one
level for every other stage, under the stage's name. The domains count the stages: their
`n_states` add up to the number of stages.
"""
function state_layout(net::ResponsiveProjectionNet)
    stages = stage_names(net)
    taken = Set(stages)
    starts = Dict{Int, _Mesh}()
    position = Dict(s => i for (i, s) in enumerate(stages))
    for m in net.meshes
        i = position[first(m.cells)]
        j = i + length(m.cells) - 1
        # a mesh is a continuous state if its cells are consecutive and its name is free
        j <= length(stages) && stages[i:j] == m.cells && !(m.name in taken) || continue
        starts[i] = m
        push!(taken, m.name)
    end
    names, domains = Symbol[], Any[]
    i = 1
    while i <= length(stages)
        m = get(starts, i, nothing)
        if m === nothing
            push!(names, stages[i])
            push!(domains, DiscreteDomain([stages[i]]))
            i += 1
        else
            push!(names, m.name)
            push!(domains, m.domain)
            i += length(m.cells)
        end
    end
    return NamedTuple{Tuple(names)}(Tuple(domains))
end

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

_count(k, one, many) = string(k, " ", k == 1 ? one : many)

function Base.show(io::IO, net::ResponsiveProjectionNet)
    print(io, "ResponsiveProjectionNet(", _count(length(stage_names(net)), "stage", "stages"), ", ",
          _count(length(net.compiled), "transition", "transitions"), ", ",
          _count(length(net.responses), "response", "responses"), ")")
end

"""
    context(net, n, pool, env)

The [`ResponseContext`](@ref) of `net` for stage vector `n`.
"""
context(net::ResponsiveProjectionNet, n::AbstractVector, pool, env) =
    ResponseContext(StageVector(n, net.groups), pool, env)

# Multiply the values `v` of the entries of transition `t` by what one of its responses
# returned: a number, a matrix laid out like the projection matrix of the net (`k` stages), or
# a function of the stage names. `rows` and `cols` are the positions of the entries in the
# projection matrix, `froms` and `tos` the names of their stages. One method per kind of
# value, so that the loop over the entries is compiled for the value at hand.
function _scale!(v::Vector{Float64}, m::Number, t, k, rows, cols, froms, tos)
    v .*= m
    return v
end

function _scale!(v::Vector{Float64}, m::AbstractMatrix, t, k, rows, cols, froms, tos)
    size(m) == (k, k) || throw(DimensionMismatch(
        "the response on :$t returned a $(size(m, 1))×$(size(m, 2)) matrix; it needs one row and one " *
        "column for each of the net's $k stages, like `to_matrix(net)`"))
    for e in eachindex(v)
        v[e] *= m[rows[e], cols[e]]
    end
    return v
end

_scale!(v::Vector{Float64}, m::AbstractArray, t, k, rows, cols, froms, tos) = throw(ArgumentError(
    "the response on :$t returned a $(typeof(m)); a response returns a number, a matrix with one row " *
    "and one column per stage, or a function (from, to) -> number"))

function _scale!(v::Vector{Float64}, m, t, k, rows, cols, froms, tos)
    for e in eachindex(v)
        v[e] *= m(froms[e], tos[e])
    end
    return v
end

# The values of the entries of one compiled transition, with its responses evaluated at `ctx`.
function _transition_values(net::ResponsiveProjectionNet, ctx, entry)
    t, rows, cols, vals, froms, tos = entry
    fs = get(net.by_transition, t, nothing)
    fs === nothing && return vals
    k = length(stage_names(net))
    v = copy(vals)
    for f in fs
        _scale!(v, f(ctx), t, k, rows, cols, froms, tos)
    end
    return v
end

function _add_entries!(A, rows, cols, values)
    for e in eachindex(values)
        A[rows[e], cols[e]] += values[e]
    end
    return A
end

function _fill_matrix!(A, net::ResponsiveProjectionNet, ctx, keep)
    for entry in net.compiled
        keep(entry[1]) || continue
        _add_entries!(A, entry[2], entry[3], _transition_values(net, ctx, entry))
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
    base = net.base
    isempty(net.by_transition) && return base
    values = copy(base.transition_values)
    for entry in net.compiled
        t = entry[1]
        old = base.transition_values[t]
        values[t] = if haskey(net.by_transition, t)
            v = _transition_values(net, ctx, entry)
            [old[e].first => v[e] for e in eachindex(old)]
        else
            copy(old)
        end
    end
    return ValuedProjectionNet{Float64}(base.net, copy(base.stage_names), values)
end

# ---------------------------------------------------------------------------
# Responses of a net whose stages have been refined
# ---------------------------------------------------------------------------

# A matrix laid out over the stages a net had before it was refined, read over the stages it
# has now: `parent[i]` is the position, among the earlier stages, of the stage that stage `i`
# descends from.
struct _PulledBack{M <: AbstractMatrix} <: AbstractMatrix{Float64}
    matrix::M
    parent::Vector{Int}
end
Base.size(p::_PulledBack) = (length(p.parent), length(p.parent))
Base.getindex(p::_PulledBack, i::Int, j::Int) = Float64(p.matrix[p.parent[i], p.parent[j]])

# A function of stage names written for the stages a net had before it was refined. For stage
# `i` of the net as it is now, it is given `names[parent[i]]`: the name of the stage that `i`
# descends from.
struct _WrittenFor{F}
    f::F
    names::Vector{Symbol}
    parent::Vector{Int}
end

function _scale!(v::Vector{Float64}, m::_WrittenFor, t, k, rows, cols, froms, tos)
    names, parent = m.names, m.parent
    for e in eachindex(v)
        v[e] *= m.f(names[parent[cols[e]]], names[parent[rows[e]]])
    end
    return v
end

# A response attached before the net was refined by `expand_stage` or `stratify`. What it
# returns refers to the stages the net had then, `names`: a matrix is laid out over them and a
# function is called with them. Both are read through `parent` (see `_PulledBack` and
# `_WrittenFor`). A number needs no translation.
struct _RefinedResponse
    f::Any
    parent::Vector{Int}
    names::Vector{Symbol}
end
(r::_RefinedResponse)(ctx) = _pull_back(r.f(ctx), r)
_pull_back(m::Number, r::_RefinedResponse) = m
_pull_back(m::AbstractArray, r::_RefinedResponse) = m       # not a matrix: `_scale!` reports it
function _pull_back(m::AbstractMatrix, r::_RefinedResponse)
    k = length(r.names)
    size(m) == (k, k) || throw(DimensionMismatch(
        "a response returned a $(size(m, 1))×$(size(m, 2)) matrix, but the net had $k stages when " *
        "the response was attached (its stages have since been refined by `expand_stage` or `stratify`)"))
    return _PulledBack(m, r.parent)
end
# refined again after being wrapped by something else: compose the two maps
_pull_back(m::_WrittenFor, r::_RefinedResponse) = _WrittenFor(m.f, m.names, m.parent[r.parent])
_pull_back(m, r::_RefinedResponse) = _WrittenFor(m, r.names, r.parent)

# `parent[i]`: the position, among the stages `names` the net had, of the one stage `i` descends from.
_refine(f, parent::Vector{Int}, names::Vector{Symbol}) = _RefinedResponse(f, parent, names)
_refine(r::_RefinedResponse, parent::Vector{Int}, names::Vector{Symbol}) =
    _RefinedResponse(r.f, r.parent[parent], r.names)

function _merge_two(a::ResponsiveProjectionNet, b::ResponsiveProjectionNet)
    base = _merge_two(a.base, b.base)
    groups = merge(a.groups, b.groups)
    return ResponsiveProjectionNet(base; responses = vcat(a.responses, b.responses),
        inflows = vcat(a.inflows, b.inflows), after = vcat(a.after, b.after),
        fecundity = union(a.fecundity, b.fecundity), groups = groups, meshes = vcat(a.meshes, b.meshes))
end
_merge_two(a::ResponsiveProjectionNet, b::ValuedProjectionNet) = _merge_two(a, ResponsiveProjectionNet(b))
_merge_two(a::ValuedProjectionNet, b::ResponsiveProjectionNet) = _merge_two(ResponsiveProjectionNet(a), b)

const _AnyNet = Union{ValuedProjectionNet, ResponsiveProjectionNet}
⊕(a::ResponsiveProjectionNet, b::_AnyNet) = _merge_two(a, b)
⊕(a::ValuedProjectionNet, b::ResponsiveProjectionNet) = _merge_two(a, b)
Base.merge(a::ResponsiveProjectionNet, b::_AnyNet, rest::_AnyNet...) = foldl(_merge_two, rest; init = _merge_two(a, b))
Base.merge(a::ValuedProjectionNet, b::ResponsiveProjectionNet, rest::_AnyNet...) =
    foldl(_merge_two, rest; init = _merge_two(a, b))

"""
    expand_stage(net::ResponsiveProjectionNet, stage, n; ageing = 1.0, name = Symbol(stage, :_ageing))

Give `stage` a fixed duration of `n` time steps (`n` at least 2) and return a responsive
net. The stages, transitions and values are those that the valued method of
[`expand_stage`](@ref) gives for the net underneath: `stage` becomes `stage1, …, stagen`,
and a new transition `name` moves individuals from each age class to the next. What is
attached to `net` is carried along:

- **Responses** stay on their transitions, whose names do not change. The new transition
  `name` has no response. A response attached before the expansion is read against the
  stages it was written for. If it returns a matrix, the matrix is laid out over those
  earlier stages, and the entry of the expanded net from stage `j` to stage `i` is
  multiplied by `M[p(i), p(j)]`, where `p` gives the earlier stage that a stage descends
  from (`p(stagek) = stage`). If it returns a function of stage names, the function is
  called with the earlier names (`stage`, not `stage1`). If it returns a number, the number
  is used unchanged. This holds through any number of refinements by `expand_stage` and
  [`stratify`](@ref).
- **Inflows** into `stage` enter its first age class, `stage1`. Other inflows are unchanged.
- **Births**: transitions marked by [`births`](@ref) stay marked. The new transition is
  not a birth.
- **After-step maps** are kept as they are.
- **Meshes** are kept, except one with `stage` among its cells, which is dropped.
- **Group totals**: in `ctx.n` and in pool contributions written with stage names,
  `stage` now stands for the total of its `n` age classes, and every other name that was
  valid before still stands for the same stages, with `stage` counted as all its age
  classes. The age classes can also be read one by one.
"""
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
    # every age class descends from `stage`; what the responses return is read accordingly
    parent = Int[]
    for (i, s) in enumerate(old)
        append!(parent, fill(i, s === stage ? n : 1))
    end
    responses = Pair{Symbol, Any}[t => _refine(f, parent, old) for (t, f) in net.responses]
    kept = _Mesh[m for m in net.meshes if !(stage in m.cells)]
    return ResponsiveProjectionNet(base; responses, inflows, after = net.after,
        fecundity = net.fecundity, groups, meshes = kept)
end

"""
    expand_stages(net::ResponsiveProjectionNet, stage => n, ...; ageing = Dict())

Apply the responsive method of [`expand_stage`](@ref) to several stages in turn, with the
default transition name for each. `ageing` maps a stage to its ageing value (default 1.0).
Responses, inflows, births, after-step maps, meshes and group totals are carried along as
by `expand_stage`.
"""
function expand_stages(net::ResponsiveProjectionNet, durations::Pair{Symbol, <:Integer}...;
        ageing::AbstractDict = Dict{Symbol, Any}())
    result = net
    for (stage, n) in durations
        result = expand_stage(result, stage, n; ageing = get(ageing, stage, 1.0))
    end
    return result
end

"""
    stratify(net::ResponsiveProjectionNet, strata; coupling = Dict(), sep = "_")

Replicate a responsive net across `strata` and return a responsive net. The stages,
transitions and values are those that the valued method of [`stratify`](@ref) gives for
the net underneath: stage `s` becomes `s_k` in each stratum `k`, transition `t` becomes
`t_k` within stratum `k`, and `coupling` adds transitions `t_from_to_to` between strata.
What is attached to `net` is carried along:

- **Responses**: a response on `t` applies to every transition derived from `t`, within
  each stratum and between strata. A response attached before the stratification is read
  against the stages it was written for. If it returns a matrix, the matrix is laid out
  over those earlier stages, and the entry of the stratified net from stage `j` to stage
  `i` is multiplied by `M[p(i), p(j)]`, where `p` gives the earlier stage of which a stage
  is a copy, in any stratum (`p(s_k) = s`). If it returns a function of stage names, the
  function is called with the earlier names (`:adult`, not `:adult_infected`). If it
  returns a number, the number is used unchanged. This holds through any number of
  refinements by `stratify` and [`expand_stage`](@ref).
- **Inflows** into a stage `s` enter its copy in the first stratum, `s_k` with
  `k = first(strata)`.
- **Births**: every transition derived from a transition marked by [`births`](@ref) is
  marked.
- **After-step maps** are kept as they are, and receive the stage vector of the
  stratified net.
- **Meshes**: each mesh `m` becomes one mesh per stratum `k`, `stratum_stage(m, k)`, whose
  cells are the copies of its cells in that stratum.
- **Group totals**: in `ctx.n` and in pool contributions written with stage names, every
  name that was valid before now stands for its total over all strata (`ctx.n[:adult]` is
  the adults of every stratum). `name_k` gives that total within stratum `k`, and the name
  of a stratum, `k`, gives everything in that stratum unless the name was already in use.
"""
function stratify(net::ResponsiveProjectionNet, strata::AbstractVector{Symbol};
        coupling::AbstractDict = Dict{Symbol, Any}(), sep = "_")
    base = stratify(net.base, strata; coupling, sep)
    m = length(stage_names(net))
    derived = Set(_ordered_transition_names(base))
    # a response on a transition applies to every transition derived from it
    names_from(t) = [stratum_transition(t, kf, kt; sep) for kf in strata for kt in strata
                     if stratum_transition(t, kf, kt; sep) in derived]
    # stage (j - 1) * m + i is stage i in stratum j; what the responses return is read accordingly
    parent = repeat(1:m, length(strata))
    old = stage_names(net)
    responses = Pair{Symbol, Any}[d => _refine(f, parent, old) for (t, f) in net.responses for d in names_from(t)]
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
    meshes = _Mesh[_Mesh((stratum_stage(m.name, k; sep), m.domain, [stratum_stage(c, k; sep) for c in m.cells]))
                   for k in strata for m in net.meshes]
    return ResponsiveProjectionNet(base; responses, inflows, after = net.after, fecundity, groups, meshes)
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
environments))` gives a `CoupledMPMProblem` with the same dynamics; with
IntegralProjectionModels.jl loaded, `lower(system, CoupledIPMTarget(n0, tspan; p =
environments))` gives a `CoupledIPMProblem` with the same dynamics, whose components are
laid out by [`state_layout`](@ref).
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

# ---------------------------------------------------------------------------
# A pooled system on a coupled problem
# ---------------------------------------------------------------------------

# Environment of a day: `p` is a sequence of environments starting at the first day, or
# a single environment used every day.
_environment(p::Union{AbstractVector, AbstractRange, Tuple}, day::Int, t0::Int) = p[day - t0 + 1]
_environment(p, day::Int, t0::Int) = p

_metadata_get(meta::NamedTuple, key::Symbol, default) = hasproperty(meta, key) ? getproperty(meta, key) : default
_metadata_get(meta::AbstractDict, key::Symbol, default) = get(meta, key, default)
_metadata_get(meta, key::Symbol, default) = default

# What a pooled system needs to run on the coupled-system engine of StructuredPopulationCore,
# whichever package steps the components. Returns
#
# - `substep`: a substep named `:pools` that computes the pool totals (and the inflows) from the
#   state at the start of the day and stores them in the system state under `:pools` and
#   `:inflows`, so that `sol.substep_log[:pools]` is the pool trajectory;
# - `matrices[name]`: a function `(system, day, p) -> (U, F)`, the survival and fecundity
#   matrices of the component's net evaluated at the day's pools;
# - `rules`: one rule per component with inflows or after-step maps, which adds the inflows and
#   applies the maps to the stepped component;
# - `inflows[name]`: with `separate_inflows`, a function `(system, day, p)` returning the day's
#   inflows of the component, for a solver that adds them itself; the rules then apply only the
#   after-step maps;
# - `state`: the initial entries of the system state.
#
# `t0` is the first day: `p` holds the environments of the days from `t0` on, or one environment.
function _coupled_pieces(sys::PooledProjectionSystem, initial_populations, t0::Int; separate_inflows::Bool = false)
    SPC = StructuredPopulationCore
    names = component_names(sys)
    Set(names) == Set(keys(initial_populations)) || throw(ArgumentError(
        "components $(names) do not match initial_populations keys $(collect(keys(initial_populations)))"))
    env(p, day) = _environment(p, day, t0)
    state_of(s) = Dict{Symbol, Vector{Float64}}(name => s[name].population for name in names)

    pools_substep = SPC.CustomSubstep(:pools, (s, day, p) -> begin
        state = state_of(s)
        pool = pool_totals(sys, state, env(p, day))
        SPC.set_state!(s, :pools, pool)
        SPC.set_state!(s, :inflows, Dict{Symbol, Vector{Float64}}(
            name => _inflows(sys[name], context(sys[name], state[name], pool, env(p, day)))
            for name in names if !isempty(sys[name].inflows)))
        pool
    end)

    matrices = Dict{Symbol, Any}()
    rules = Any[]
    inflows = Dict{Symbol, Any}()
    for name in names
        net = sys[name]
        matrices[name] = (s, day, p) -> survival_fecundity_matrices(net,
            context(net, s[name].population, SPC.get_state(s, :pools), env(p, day)))
        separate = separate_inflows && !isempty(net.inflows)
        separate && (inflows[name] = (s, day, p) -> SPC.get_state(s, :inflows)[name])
        if (!isempty(net.inflows) && !separate) || !isempty(net.after)
            push!(rules, SPC.CustomRule(Symbol(name, :_inflow_and_after), (s, day, p) -> begin
                stepped = s[name].population
                wanted = (separate || isempty(net.inflows)) ? stepped : stepped .+ SPC.get_state(s, :inflows)[name]
                wanted = _after(net, wanted)
                [SPC.StageFlux(name, i, wanted[i] - stepped[i]) for i in eachindex(stepped) if wanted[i] != stepped[i]]
            end))
        end
    end
    state = Dict{Symbol, Any}(:pools => NamedTuple(), :inflows => Dict{Symbol, Vector{Float64}}())
    return (substep = pools_substep, matrices = matrices, rules = rules, inflows = inflows, state = state)
end
