"""
Open communities: pooled systems with ports, composed along undirected wiring diagrams.

A [`PooledProjectionSystem`](@ref) is closed: its components and pools are fixed when it is
built. This file makes it open. An [`OpenCommunity`](@ref) is one or more components
(species) whose responses read, and whose stages contribute to, named pools, some of which
are exposed as ports. Open communities compose along an undirected wiring diagram: each box
is filled by a community, each junction is one pool whose total is the sum of what every
attached species contributes, and the outer ports of the diagram are the pools of the
composite. Composites nest, and each species keeps its own stages and responses, written
with its own names for the pools. Flattened, a community is a `PooledProjectionSystem`
([`system`](@ref)), whose state is a flat vector with one block of stages per species.

This is the discrete-time resource-sharer pattern of matrix community models (Lytle &
Tonkin 2023), where each box's update depends on the totals of its junctions.
"""

# A view of the pool totals under a component's own (local) pool names.
struct PoolView{P <: NamedTuple}
    pool::P
    alias::Dict{Symbol, Symbol}
end
Base.getproperty(v::PoolView, name::Symbol) =
    getfield(getfield(v, :pool), get(getfield(v, :alias), name, name))
Base.getindex(v::PoolView, name::Symbol) = getproperty(v, name)
Base.haskey(v::PoolView, name::Symbol) = haskey(getfield(v, :pool), get(getfield(v, :alias), name, name))

"""
    OpenCommunity

One or more species with exposed pools (its ports). Build one species with
[`species`](@ref), and join them with [`community`](@ref) or [`compose`](@ref).

The flattened model is a `PooledProjectionSystem`, available from [`system`](@ref). The
state of a community is a flat vector: one block of stages per species, in the order of
[`species_names`](@ref) (see [`state_vector`](@ref)). `length(c)` is the number of states,
and `c[name]` the responsive net of a species, with its responses reading the pools of the
composite.
"""
struct OpenCommunity
    names::Vector{Symbol}
    nets::Dict{Symbol, ResponsiveProjectionNet}
    aliases::Dict{Symbol, Dict{Symbol, Symbol}}
    contributions::Vector{Tuple{Symbol, Symbol, Any}}
    ports::Vector{Symbol}
    diagram::Any
    system::PooledProjectionSystem
    layout::StructuredPopulationCore.StateBlockLayout
end

function _open(names, nets, aliases, contributions, ports, diagram)
    components = map(names) do name
        net, alias = nets[name], aliases[name]
        if all(k == v for (k, v) in alias)
            name => net
        else
            # responses were written with the species' own pool names: translate them
            local_view(f) = ctx -> f(ResponseContext(ctx.n, PoolView(ctx.pool, alias), ctx.env))
            name => ResponsiveProjectionNet(net.base;
                responses = Pair{Symbol, Any}[t => local_view(f) for (t, f) in net.responses],
                inflows = Pair{Symbol, Any}[s => local_view(f) for (s, f) in net.inflows],
                after = net.after, fecundity = net.fecundity, groups = net.groups, meshes = meshes(net))
        end
    end
    pool_order = copy(ports)
    for (pool, _, _) in contributions
        pool in pool_order || push!(pool_order, pool)
    end
    pools = [Pool(p, Pair{Symbol, Any}[c => w for (q, c, w) in contributions if q === p]) for p in pool_order]
    sys = PooledProjectionSystem(components...; pools = pools)
    layout = StructuredPopulationCore.StateBlockLayout(collect(Symbol, names),
                                                       [length(stage_names(nets[n])) for n in names])
    return OpenCommunity(collect(Symbol, names), nets, aliases, contributions, collect(Symbol, ports), diagram, sys, layout)
end

"""
    species(name, net; occupies = [], reads = [])

A single species as an [`OpenCommunity`](@ref). `net` is a valued or responsive projection
net. `occupies` lists `pool => contribution` pairs saying how much of each pool the species
occupies; a contribution is a vector of weights (one per stage), a list of `stage =>
weight` pairs, a number (weight on every stage), or a function `(n, env) -> number`.
`reads` names pools that the species' responses read without contributing to them.

```julia
grass = species(:grass, respond(life, :seeding => ctx -> max(0, 1 - ctx.pool.space / 1000));
                occupies = [:space => [:seedling => 0.1, :adult => 1.0]])
```

A pool can also hold one value for each of a set of classes, such as the prey on offer to
predators of each size class: a contribution is then a matrix of weights, one row per
class and one column per stage, or a function `(n, env) -> vector`, and a response reads
the pool as `ctx.pool.name[i]`. Every contribution to such a pool is a vector of the same
length (see `Pool`), and [`pool_totals`](@ref) gives the pool as a vector.
"""
function species(name::Symbol, net; occupies = Pair{Symbol, Any}[], reads = Symbol[])
    r = ResponsiveProjectionNet(net)
    pools = Symbol[p.first for p in occupies]
    allunique(pools) || throw(ArgumentError("species :$name lists a pool twice"))
    ports = vcat(pools, [p for p in reads if !(p in pools)])
    contributions = Tuple{Symbol, Symbol, Any}[(p.first, name, p.second) for p in occupies]
    return _open([name], Dict(name => r), Dict(name => Dict(p => p for p in ports)), contributions, ports, nothing)
end

"""
    subcommunity(c, names...)

The named species of community `c` as a community of their own, keeping the pools they
are attached to: for example the natives of a fish community without the non-natives, or
one species on its own as an invader.
"""
function subcommunity(c::OpenCommunity, names::Symbol...)
    all(n -> n in c.names, names) || throw(ArgumentError("not all of $(names) are species of this community"))
    keep = [n for n in c.names if n in names]
    aliases = Dict(n => c.aliases[n] for n in keep)
    contributions = Tuple{Symbol, Symbol, Any}[x for x in c.contributions if x[2] in keep]
    used = unique(vcat([collect(values(aliases[n])) for n in keep]..., [x[1] for x in contributions]))
    ports = [p for p in pool_names(c.system) if p in used]
    return _open(keep, Dict(n => c.nets[n] for n in keep), aliases, contributions, ports, nothing)
end

"""
    system(c)

The `PooledProjectionSystem` of a community: its species as responsive projection nets,
and its pools.
"""
system(c::OpenCommunity) = c.system

"""
    species_names(c)

Names of the species of a community, in state order.
"""
species_names(c::OpenCommunity) = c.names

"""
    stage_names(c, species)

Stage names of `species` in a community.
"""
stage_names(c::OpenCommunity, sp::Symbol) = stage_names(c.nets[sp])

"""
    pool_names(c; internal = false)

Names of the pools a community exposes; with `internal = true`, all of its pools,
including those shared only inside it.
"""
pool_names(c::OpenCommunity; internal::Bool = false) = internal ? pool_names(c.system) : c.ports

"""
    diagram(c)

The undirected wiring diagram a community was composed along, or `nothing` for a single
species.
"""
diagram(c::OpenCommunity) = c.diagram

Base.length(c::OpenCommunity) = length(c.layout)
Base.getindex(c::OpenCommunity, sp::Symbol) = c.system[sp]

function Base.show(io::IO, c::OpenCommunity)
    print(io, "OpenCommunity(", join(c.names, ", "), "; pools = ", join(c.ports, ", "), ")")
end

const _JUNCTION_COUNTER = Ref(0)

"""
    compose(diagram, components)

Compose open communities along an undirected wiring diagram. Box `b` is filled by
`components[b]`, whose pools are matched to the box's ports in order. Each junction is one
pool: its total is the sum of what every attached species contributes. Outer ports of the
diagram are the pools of the composite; junctions that are not exposed are shared only
inside it.

A junction is named by its variable in the diagram (as in a diagram written with
`@relation`), or else by the first pool attached to it. A species' responses keep reading
their pools under the names the species gave them. Composites nest: a component may itself
be a composite.

This is a method of Catlab's `compose`.
"""
function compose(d::UndirectedWiringDiagram, components::AbstractVector{<:OpenCommunity})
    nb = nparts(d, :Box)
    nb == length(components) ||
        throw(DimensionMismatch("diagram has $nb boxes, got $(length(components)) components"))
    comps = OpenCommunity[c for c in components]
    boxports = [collect(ports(d, b)) for b in 1:nb]
    for b in 1:nb
        length(boxports[b]) == length(comps[b].ports) || throw(DimensionMismatch(
            "box $b has $(length(boxports[b])) ports but its component exposes $(length(comps[b].ports))"))
    end
    nj = nparts(d, :Junction)
    portjunction = [[junction(d, p) for p in boxports[b]] for b in 1:nb]
    outer = [junction(d, q; outer = true) for q in 1:nparts(d, :OuterPort)]
    jnames = _junction_names(d, comps, portjunction, nj)
    for j in 1:nj
        # a junction that is not exposed gets a name nothing outside can clash with
        j in outer || (jnames[j] = Symbol(jnames[j], "#", _JUNCTION_COUNTER[] += 1))
    end

    names = Symbol[]
    nets = Dict{Symbol, ResponsiveProjectionNet}()
    aliases = Dict{Symbol, Dict{Symbol, Symbol}}()
    contributions = Tuple{Symbol, Symbol, Any}[]
    for b in 1:nb
        c = comps[b]
        rename = Dict(c.ports[i] => jnames[j] for (i, j) in enumerate(portjunction[b]))
        for name in c.names
            name in names && throw(ArgumentError("species :$name appears twice in the composite"))
            push!(names, name)
            nets[name] = c.nets[name]
            aliases[name] = Dict(k => get(rename, v, v) for (k, v) in c.aliases[name])
        end
        for (pool, name, w) in c.contributions
            push!(contributions, (get(rename, pool, pool), name, w))
        end
    end
    return _open(names, nets, aliases, contributions, Symbol[jnames[j] for j in outer], d)
end

function _junction_names(d, comps, portjunction, nj)
    vars = try
        subpart(d, :variable)
    catch
        nothing
    end
    vars !== nothing && eltype(vars) == Symbol && return collect(Symbol, vars)
    names = Vector{Symbol}(undef, nj)
    for (b, js) in enumerate(portjunction), (i, j) in enumerate(js)
        isassigned(names, j) || (names[j] = comps[b].ports[i])
    end
    return names
end

"""
    community(components...)

Compose open communities that share pools by name: every pool named by any component
becomes one junction, exposed as a pool of the result. The wiring diagram that was
generated is available from [`diagram`](@ref).
"""
function community(components::OpenCommunity...)
    pools = Symbol[]
    for c in components, p in c.ports
        p in pools || push!(pools, p)
    end
    d = RelationDiagram(length(pools))
    js = add_junctions!(d, length(pools); variable = pools)
    for c in components
        b = add_box!(d, length(c.ports); name = first(c.names))
        set_junction!(d, ports(d, b), [findfirst(==(p), pools) for p in c.ports])
    end
    set_junction!(d, js; outer = true)
    return compose(d, collect(components))
end

# ---------------------------------------------------------------- state

# The state of a community is a flat vector, one block of stages per species; its system's
# state is a dictionary from species name to stage vector.
_split(c::OpenCommunity, n::AbstractVector) =
    Dict{Symbol, Vector{Float64}}(sp => collect(Float64, n[c.layout[sp]]) for sp in c.names)
_join(c::OpenCommunity, state::AbstractDict) = reduce(vcat, [state[sp] for sp in c.names])

"""
    state_vector(c, species => stages, ...)
    state_vector(c, n)

The flat state vector of a community from one stage vector per species. The second form
takes a state given either way, as a flat vector (checked for length and copied) or as a
vector of `species => stages` pairs; functions that accept a community state use it.
See also [`species_states`](@ref).
"""
function state_vector(c::OpenCommunity, blocks::Pair{Symbol}...)
    d = Dict(blocks)
    Set(keys(d)) == Set(c.names) || throw(ArgumentError("need one stage vector for each of $(c.names)"))
    n = reduce(vcat, [collect(Float64, d[sp]) for sp in c.names])
    length(n) == length(c) || throw(DimensionMismatch("stage vectors do not match the community's stages"))
    return n
end
state_vector(c::OpenCommunity, n::AbstractVector{<:Real}) =
    length(n) == length(c) ? collect(Float64, n) :
    throw(DimensionMismatch("state has length $(length(n)), community has $(length(c)) states"))
state_vector(c::OpenCommunity, n::AbstractVector{<:Pair}) = state_vector(c, n...)

"""
    species_states(c, n)

The state `n` of a community (a flat vector, or `species => stages` pairs) as a dictionary
from species name to stage vector: the form its [`system`](@ref) uses. The inverse of
[`state_vector`](@ref).
"""
species_states(c::OpenCommunity, n::AbstractVector) = _split(c, state_vector(c, n))

# internal names kept for code written against 0.1.5
const _state = state_vector
"""
    pool_totals(c, n, env; internal = false)

Totals of the pools a community exposes, in state `n` (a flat vector, or `species =>
stages` pairs), as a `NamedTuple`; with `internal = true`, of all of its pools.
"""
function pool_totals(c::OpenCommunity, n::AbstractVector, env; internal::Bool = false)
    all_pools = pool_totals(c.system, _split(c, _state(c, n)), env)
    internal && return all_pools
    return NamedTuple{Tuple(c.ports)}(Tuple(all_pools[p] for p in c.ports))
end

"""
    advance(c, n, env; rng = nothing)

Advance a closed community one time step from state `n` (a flat vector, or `species =>
stages` pairs), returning the new flat state: [`advance`](@ref) of its
[`system`](@ref).

With `rng` (a random number generator), the step has demographic stochasticity:
individuals are whole, each survives and moves according to a multinomial draw from its
column of the survival matrix, and births and inflows are Poisson with the deterministic
values as means. This needs whole numbers in `n`, the births of each species marked with
`births`, and survival matrices whose columns sum to at most one. The numbers are drawn
for each species in turn: survival, births, inflows.
"""
function advance(c::OpenCommunity, n::AbstractVector, env; rng = nothing)
    state = _split(c, _state(c, n))
    rng === nothing && return _join(c, advance(c.system, state, env))
    return _join(c, _demographic_advance(c.system, state, env, rng))
end

# One step with demographic stochasticity: individuals are whole, survival and movement are
# a multinomial draw down each column of U, births and inflows are Poisson.
function _demographic_advance(sys::PooledProjectionSystem, state, env, rng)
    pool = pool_totals(sys, state, env)
    next = Dict{Symbol, Vector{Float64}}()
    for name in component_names(sys)
        net, n = sys[name], state[name]
        all(isinteger, n) || throw(ArgumentError(
            "demographic stochasticity needs whole numbers of individuals in :$name"))
        ctx = context(net, n, pool, env)
        U, F = survival_fecundity_matrices(net, ctx)
        worst = maximum(sum(U; dims = 1))
        worst <= 1 + 1e-6 || throw(ArgumentError(
            "survival matrix of :$name has a column summing to $worst; demographic stochasticity needs " *
            "survival probabilities (column sums at most 1). Mark births with `births(net, ...)`"))
        counts = StructuredPopulationCore.demographic_step!(rng, zeros(Int, length(n)), round.(Int, n), U, F)
        stepped = Float64.(counts)
        for (i, r) in enumerate(_inflows(net, ctx))
            r > 0 && (stepped[i] += StructuredPopulationCore.rand_poisson(rng, r))
        end
        next[name] = collect(Float64, _after(net, stepped))
    end
    return next
end
