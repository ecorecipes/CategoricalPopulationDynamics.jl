# Responsive Nets & Pooled Systems

A `ValuedProjectionNet` holds numbers. In a community, some of those numbers depend on what the rest of the community is doing: fecundity falls as shared space fills, mortality rises with the number of parasites. Three things say this at the level of named transitions, without a hand-written simulation loop.

- A **responsive net** is a valued net whose named transitions carry *responses*. A response is a function of a context, and what it returns scales the values of its transition at each time step.
- A **pool** is a named total, such as the space taken, to which components contribute and which responses can read.
- A **pooled system** is a set of named components together with the pools that link them. This is a community: no component refers to another directly, only to the pools.

A pooled system has a definite meaning for one time step, given by [`advance`](@ref), and with MatrixProjectionModels.jl it lowers to a `CoupledMPMProblem` that has the same dynamics; with IntegralProjectionModels.jl, to a `CoupledIPMProblem` that has them too.

## A life cycle that responds to a pool

```@docs
ResponsiveProjectionNet
respond
births
```

```@example catpd
using CategoricalPopulationDynamics

life = ValuedProjectionNet([:juvenile, :adult],
    :maturing  => [(:juvenile => :adult) => 0.3],
    :surviving => [(:adult => :adult) => 0.5],
    :breeding  => [(:adult => :juvenile) => 6.0])

K = 1000.0
crowding(ctx) = max(0.0, 1 - ctx.pool.space / K)

plant = births(respond(life, :breeding => crowding), :breeding)
```

`respond` attaches `crowding` to the transition `:breeding`: breeding has its full value while no space is taken, and stops once `K` units are. `births` marks `:breeding` as a birth, which matters only when the matrix is split into its survival and fecundity parts.

Nothing is evaluated yet. `stage_names`, `transition_names` and `to_matrix` apply to a responsive net as they do to a valued net, and without a context `to_matrix` gives the matrix of the net underneath, with no response applied:

```@example catpd
to_matrix(plant) == to_matrix(life)
```

## The context

```@docs
ResponseContext
StageVector
context
```

In a system, a context is made for each component at each time step. `context` makes one by hand, which is the way to try a response out:

```@example catpd
ctx = context(plant, [10.0, 20.0], (space = 400.0,), nothing)
(ctx.n[:adult], ctx.n[2], ctx.pool.space)
```

`ctx.n` holds the component's own stages and can be indexed by name or by position. It is otherwise an ordinary vector, so `sum(ctx.n)` is the size of the population. `ctx.pool` holds the pool totals by name, and `ctx.env` the environment of the time step, which is `nothing` here.

## The matrix at a context

Three functions evaluate the responses of a net at a context. `to_matrix(net, ctx)` gives the projection matrix; its docstring is listed with the other methods of [`to_matrix`](@ref), under [Valued Projection Nets](valued.md). The other two are listed here.

```@docs
survival_fecundity_matrices(::ResponsiveProjectionNet, ::ResponseContext)
evaluate(::ResponsiveProjectionNet, ::ResponseContext)
```

```@example catpd
to_matrix(plant, ctx)
```

With 400 of the 1000 units of space taken, breeding is 6 × 0.6 = 3.6. The transitions without a response keep their values. Because `:breeding` is marked as a birth, the matrix splits into a survival part `U`, here `[0 0; 0.3 0.5]`, and a fecundity part `F`:

```@example catpd
U, F = survival_fecundity_matrices(plant, ctx)
F
```

`evaluate` gives the model frozen at that moment as a plain `ValuedProjectionNet`, with each value still attached to its named transition:

```@example catpd
frozen = evaluate(plant, ctx)
transition_matrix(frozen, :breeding)
```

Responsive nets combine with `⊕` (or `merge`), with each other and with valued nets, so a life cycle can be put together from modules that bring their own responses:

```@example catpd
survive = ValuedProjectionNet([:juvenile, :adult],
    :maturing  => [(:juvenile => :adult) => 0.3],
    :surviving => [(:adult => :adult) => 0.5])
breed = respond(ValuedProjectionNet([:juvenile, :adult],
    :breeding => [(:adult => :juvenile) => 6.0]), :breeding => crowding)

to_matrix(survive ⊕ breed, ctx) == to_matrix(plant, ctx)
```

## What a response returns

A response returns a number, a matrix or a function of stage names. The three are shown on a life cycle with three stages.

```@example catpd
life3 = ValuedProjectionNet([:egg, :juvenile, :adult],
    :hatching  => [(:egg => :juvenile) => 0.5],
    :maturing  => [(:juvenile => :adult) => 0.3],
    :surviving => [(:juvenile => :juvenile) => 0.2, (:adult => :adult) => 0.5],
    :breeding  => [(:adult => :egg) => 6.0])
to_matrix(life3)
```

**A number** scales every entry of the transition. The context `c` made here serves all the nets of this section, since they have the same stages.

```@example catpd
halved = respond(life3, :breeding => ctx -> 0.5)
c = context(halved, [10.0, 20.0, 30.0], (space = 0.5,), nothing)
to_matrix(halved, c)
```

**A matrix** with one row and one column per stage, laid out like `to_matrix(net)`, scales each entry by its own factor: the entry from stage `j` to stage `i` is multiplied by `M[i, j]`.

```@example catpd
M = [0.9 0.6 0.4;
     0.7 0.8 0.3;
     0.2 0.1 0.5]
to_matrix(respond(life3, :surviving => ctx -> M), c)
```

`:surviving` has two entries, juveniles that stay juveniles and adults that stay adults, so `M[2, 2]` and `M[3, 3]` are used: 0.2 × 0.8 = 0.16 and 0.5 × 0.5 = 0.25. The other values of `M` are ignored. Any `AbstractMatrix` will do, for example a `Diagonal`.

**A function** `(from, to) -> number` of the stage names is called for each entry of the transition. Here adults survive at a tenth of their rate, 0.5 × 0.1 = 0.05, and juveniles as before:

```@example catpd
to_matrix(respond(life3, :surviving => ctx -> ((from, to) -> from === :adult ? 0.1 : 1.0)), c)
```

A matrix and a function can say the same thing. Below, three transitions are scaled by `M`, and breeding by the pool `:space` as well, first with matrices and then with functions of the stage names.

```@example catpd
index = Dict(:egg => 1, :juvenile => 2, :adult => 3)

by_matrix = respond(life3,
    :surviving => ctx -> M,
    :hatching  => ctx -> M,
    :breeding  => ctx -> ctx.pool.space .* M)
by_name = respond(life3,
    :surviving => ctx -> ((from, to) -> M[index[to], index[from]]),
    :hatching  => ctx -> ((from, to) -> M[index[to], index[from]]),
    :breeding  => ctx -> ((from, to) -> ctx.pool.space * M[index[to], index[from]]))

A = to_matrix(by_matrix, c)
```

Hatching is 0.5 × `M[2, 1]` = 0.35, and breeding is 6 × 0.5 × `M[1, 3]` = 1.2, where 0.5 is the value of the pool. `:maturing` has no response and stays at 0.3. The functions give the same matrix:

```@example catpd
to_matrix(by_name, c) == A
```

Several responses on one transition multiply, whatever their kinds. Two more responses on `:breeding`, a number and a function whose product is one, leave the matrix as it was:

```@example catpd
more = respond(by_matrix, :breeding => ctx -> 0.5, :breeding => ctx -> ((from, to) -> 2.0))
to_matrix(more, c) == A
```

A response scales the entries that its transition has. It does not add entries: a matrix full of twos on `:maturing` doubles the one entry of that transition and nothing else.

```@example catpd
to_matrix(respond(life3, :maturing => ctx -> fill(2.0, 3, 3)), c)
```

A matrix that does not have one row and one column per stage is a `DimensionMismatch`, and an array that is not a matrix is an `ArgumentError`. Both are thrown when the response is evaluated, by `to_matrix(net, ctx)`, `evaluate` or `advance`. A response for a transition that the net does not have is an `ArgumentError` from `respond`.

## Pools and pooled systems

```@docs
Pool
PooledProjectionSystem
pool_names
pool_totals
advance
trajectory
```

Two plants compete for space. Each has its own life cycle, and the seeding of each falls as space fills, through the response `crowding` used above. Neither refers to the other. The pool `:space` adds up what they take: the grass 0.1 per seedling and 1 per adult, written with stage names, and the shrub 0.1, 1 and 4 per seedling, juvenile and adult, written as one weight per stage.

```@example catpd
grass = respond(ValuedProjectionNet([:seedling, :adult],
        :establishing => [(:seedling => :adult) => 0.30],
        :persisting   => [(:adult => :adult) => 0.50],
        :seeding      => [(:adult => :seedling) => 6.0]),
    :seeding => crowding)
shrub = respond(ValuedProjectionNet([:seedling, :juvenile, :adult],
        :establishing => [(:seedling => :juvenile) => 0.30],
        :maturing     => [(:juvenile => :adult) => 0.50],
        :persisting   => [(:adult => :adult) => 0.95],
        :seeding      => [(:adult => :seedling) => 3.0]),
    :seeding => crowding)

space = Pool(:space, :grass => [:seedling => 0.1, :adult => 1.0], :shrub => [0.1, 1.0, 4.0])
com = PooledProjectionSystem(:grass => grass, :shrub => shrub; pools = [space])
```

```@example catpd
(component_names(com), pool_names(com), stage_names(com, :shrub))
```

The state of a system is a dictionary from the name of each component to its stage vector. `pool_totals` gives the pools for a state:

```@example catpd
state = Dict(:grass => [50.0, 10.0], :shrub => [5.0, 0.0, 1.0])
pool_totals(com, state, nothing)
```

That is 0.1 × 50 + 10 for the grass and 0.1 × 5 + 4 × 1 for the shrub. `advance` takes the system one step forward:

```@example catpd
next = advance(com, state, nothing)
(grass = next[:grass], shrub = next[:shrub])
```

The crowding factor is 1 − 19.5 / 1000 = 0.9805 for both plants. The grass has 6 × 0.9805 × 10 = 58.83 seedlings and 0.3 × 50 + 0.5 × 10 = 20 adults; the shrub has 3 × 0.9805 × 1 = 2.9415 seedlings, 0.3 × 5 = 1.5 juveniles and 0.95 adults. Every component is updated from the same state, so the order of the components does not matter.

`trajectory` repeats the step, once for each environment it is given, and returns the states and the pool totals used at each step:

```@example catpd
out = trajectory(com, state, fill(nothing, 400))
(length(out.states), length(out.pools))
```

```@example catpd
[(t = t,
  grass = round(sum(out.states[t + 1][:grass]); digits = 1),
  shrub = round(sum(out.states[t + 1][:shrub]); digits = 1),
  space = round(out.pools[t + 1].space; digits = 1)) for t in (0, 10, 25, 50, 100, 200)]
```

Each plant replaces itself exactly at one value of the crowding factor `1 - space / K`: 1/3.6 for the grass and 1/9 for the shrub. The grass therefore stops growing when about 722 units of space are taken, the shrub only at about 889. The grass grows first and fills the space to about 720 within ten steps. The shrub goes on growing there, and as it takes more space the grass falls below replacement and dies out. Space settles at the shrub's threshold, `K * (1 - 1/9)`:

```@example catpd
final = out.states[end]
(space = pool_totals(com, final, nothing).space, grass = sum(final[:grass]))
```

A contribution to a pool can also be a number, which weights every stage alike, or a function of the component's `StageVector` and the environment. Below, each grass plant counts once, and the adult shrubs are multiplied by the environment, which is 2.0:

```@example catpd
counts = Pool(:individuals, :grass => 1.0, :shrub => (n, env) -> env * n[:adult])
counted = PooledProjectionSystem(:grass => grass, :shrub => shrub; pools = [space, counts])
pool_totals(counted, state, 2.0)
```

The environment is the last argument of `pool_totals` and `advance`, and `trajectory` takes one environment per step. It reaches responses and inflows as `ctx.env`, and contributions that are functions as their second argument. Here the grass sets half its seed in a dry step; the response to rain multiplies the response to crowding that the grass already has.

```@example catpd
rainfed = respond(grass, :seeding => ctx -> ctx.env.rain)
wet_or_dry = PooledProjectionSystem(:grass => rainfed, :shrub => shrub; pools = [space])

(wet = advance(wet_or_dry, state, (rain = 1.0,))[:grass],
 dry = advance(wet_or_dry, state, (rain = 0.5,))[:grass])
```

A component may be a plain valued net, which has no responses. The constructor checks the system: a pool that lists a component the system does not have, and two components or two pools with one name, are `ArgumentError`s; a vector of weights that does not have one weight per stage, or a matrix of weights that does not have one column per stage, is a `DimensionMismatch`.

### Pools with a value for each class

Some interactions need more than one number. Predation that depends on the sizes of predator and prey, for example, needs for each size class of predator the prey of suitable size on offer. A pool can hold such a vector. Its contributions are then vectors of one length, and the pool is their sum. A contribution is a matrix of weights, with one row for each element of the pool and one column per stage of the component, or a function `(n, env)` of the stage vector and the environment that returns a vector. A response reads element `i` of the pool as `ctx.pool.name[i]`.

Below, shade is counted in two height classes. A grass adult casts shade in the lower class; a shrub juvenile casts shade in the lower class and a shrub adult four units in the upper one. Grass seeding falls with the shade above it.

```@example catpd
shade = Pool(:shade, :grass => [0.0 1.0; 0.0 0.0], :shrub => [0.0 1.0 0.0; 0.0 0.0 4.0])
shaded = respond(grass, :seeding => ctx -> exp(-ctx.pool.shade[2] / 100))
canopy = PooledProjectionSystem(:grass => shaded, :shrub => shrub; pools = [space, shade])
pool_totals(canopy, state, nothing)
```

The lower class holds the 10 grass adults and no shrub juveniles; the upper one 4 × 1 for the shrub adult. A scalar pool such as `:space` is unchanged by a vector pool beside it. The step uses the vector like any other pool:

```@example catpd
advance(canopy, state, nothing)[:grass]
```

One pool cannot mix numbers and vectors, and its vectors must have one length: either is an error when the pool is computed. A pool without contributions is `0.0`. `trajectory` returns the vectors among the pools of each step, and the lowered problems log them in `substep_log[:pools]`.

## Inflows and after-step maps

```@docs
inflow
after_step
```

An inflow adds individuals to a stage at each step, whatever the component's own abundance, as immigration or a seed rain does. An after-step map is applied to the component's new stage vector once the step is done. Here the plant of the first section receives seeds in proportion to the space taken, and numbers are rounded down to whole individuals:

```@example catpd
seeded = inflow(plant, :juvenile => ctx -> 0.01 * ctx.pool.space)
seeded = after_step(seeded, n -> floor.(n))
meadow = PooledProjectionSystem(:plant => seeded;
                                pools = [Pool(:space, :plant => [:adult => 1.0])])

advance(meadow, Dict(:plant => [10.0, 250.0]), nothing)[:plant]
```

The pool is 250, so breeding is 6 × 0.75 = 4.5. The matrix gives 4.5 × 250 = 1125 juveniles and 0.3 × 10 + 0.5 × 250 = 128 adults, the inflow adds 0.01 × 250 = 2.5 juveniles, and the after-step map rounds 1127.5 down to 1127.

The inflow is evaluated at the same context as the matrix, that of the state before the step. An after-step map receives the new stage vector as a plain vector, without names.

## Refining the life cycle

`expand_stage` and `stratify`, described under [Stage Durations & Strata](stage_structure.md), accept a responsive net and return one. What is attached to the net is carried along, so a model written for a simple life cycle keeps working as the life cycle is refined:

- a response on a transition acts on every transition derived from it, within each stratum and between strata;
- transitions marked as births stay marked;
- an inflow into a stage that is given a duration enters its first age class, and after `stratify` inflows enter the first stratum;
- after-step maps are kept as they are, so they should not depend on the number or the order of the stages;
- the earlier names stay valid in `ctx.n`, and in pool contributions written with stage names, where they now stand for totals.

Juveniles of the plant now take three steps to mature:

```@example catpd
aged = expand_stage(plant, :juvenile, 3; ageing = 0.9)
c3 = context(aged, [1.0, 2.0, 3.0, 20.0], (space = 400.0,), nothing)
(c3.n[:juvenile], c3.n[:juvenile2], c3.n[:adult])
```

`c3.n[:juvenile]` is the total of the three age classes, 1 + 2 + 3. Breeding still responds to crowding, and now enters the first age class:

```@example catpd
to_matrix(aged, c3)
```

The net is then replicated across two strata, and half of the healthy juveniles that mature join the infected stratum:

```@example catpd
strat = stratify(aged, [:healthy, :infected];
                 coupling = Dict(:maturing => [0.5 0.0; 0.5 1.0]))
c8 = context(strat, collect(1.0:8.0), (space = 400.0,), nothing)

[name => c8.n[name] for name in (:adult, :adult_infected, :juvenile, :juvenile_healthy,
                                 :infected, :juvenile2_infected)]
```

The eight stages hold 1 to 8 individuals, in the order of `stage_names(strat)`. Every earlier name is still there: `:adult` is the total over both strata, `:juvenile` the total of the three age classes in both strata, `:juvenile_healthy` the three age classes of one stratum, and `:infected` everything in the infected stratum.

```@example catpd
to_matrix(strat, c8)
```

Breeding responds to crowding in both strata, at 3.6, and the births are still told apart from the rest:

```@example catpd
U, F = survival_fecundity_matrices(strat, c8)
findall(!iszero, F)
```

A pool whose contributions are written with stage names needs no change either: `:adult` is read as the adults of both strata, 4 + 8 = 12. A vector of weights would have to be rewritten, since it needs one weight per stage.

```@example catpd
refined = PooledProjectionSystem(:plant => strat;
                                 pools = [Pool(:space, :plant => [:adult => 1.0])])
pool_totals(refined, Dict(:plant => collect(1.0:8.0)), nothing)
```

A matrix or a function of stage names refers to the stages the net had when the response was attached. Neither has to change when the net is refined: every entry of the refined net takes the factor of the entry it derives from. Eggs of `by_matrix`, from the section on what a response returns, now last three steps:

```@example catpd
aged3 = expand_stage(by_matrix, :egg, 3; ageing = 0.9)
c5 = context(aged3, collect(1.0:5.0), (space = 0.5,), nothing)
to_matrix(aged3, c5)
```

`M` is still the 3 × 3 matrix over `:egg`, `:juvenile` and `:adult`. Hatching, which now leaves `:egg3`, takes `M[2, 1]` and is 0.35 as before; breeding, which now enters `:egg1`, takes `M[1, 3]` and is 1.2 as before. The ageing transition is new and has no response.

A response attached after the refinement is written for the refined stages. Its matrix has one row and one column for each of the five stages:

```@example catpd
slower = respond(aged3, :egg_ageing => ctx -> fill(0.5, 5, 5))
to_matrix(slower, c5)
```

The same holds for functions of stage names. A function attached before `stratify` goes on being called with the names it was written for, `:adult` and not `:adult_infected`, so adults survive at 0.05 in both strata:

```@example catpd
named = respond(life3, :surviving => ctx -> ((from, to) -> from === :adult ? 0.1 : 1.0))
strata = stratify(named, [:healthy, :infected])
c6 = context(strata, ones(6), (space = 0.5,), nothing)
to_matrix(strata, c6)
```

A function attached to the stratified net sees the names of that net. It multiplies the earlier response, so infected adults survive at 0.5 × 0.1 × 0.5 = 0.025:

```@example catpd
late = respond(strata,
    :surviving_infected => ctx -> ((from, to) -> from === :adult_infected ? 0.5 : 1.0))
to_matrix(late, c6)
```

The two operations can be applied in either order and more than once. Each response goes on being read against the stages of the net it was attached to.

## Open communities

A pooled system is closed: its components and pools are fixed when it is built. An *open community* is a pooled system with ports. Each species says which pools it occupies, and how much of each, and which it only reads; those pools are its ports. Open communities compose along an undirected wiring diagram, as in matrix community models (Lytle & Tonkin 2023): each box is filled by a community, each junction is one pool whose total is the sum of what every attached species contributes, and the outer ports of the diagram are the pools of the composite. Composites nest, and every species keeps its own stages and responses, written with its own names for the pools. Flattened, a community is a `PooledProjectionSystem`, and its state is a flat vector with one block of stages per species.

```@docs
OpenCommunity
species
community
compose(::CategoricalPopulationDynamics.UndirectedWiringDiagram, ::AbstractVector{<:OpenCommunity})
subcommunity
system
species_names
diagram(::OpenCommunity)
state_vector
species_states
```

`stage_names`, `pool_names`, `pool_totals` and `advance` also take a community; their methods are listed with the others above. The two plants of the section on pools, as species:

```@example catpd
g = species(:grass, grass; occupies = [:space => [:seedling => 0.1, :adult => 1.0]])
s = species(:shrub, shrub; occupies = [:space => [0.1, 1.0, 4.0]])
meadow2 = community(g, s)
```

`community` joins species that share pools by name. The result is the system built by hand above, and one step of it is one step of that system:

```@example catpd
n = state_vector(meadow2, :grass => [50.0, 10.0], :shrub => [5.0, 0.0, 1.0])
(pool_totals(meadow2, n, nothing), advance(meadow2, n, nothing) == vcat(next[:grass], next[:shrub]))
```

A wiring diagram says what is shared explicitly. Here the junction is called `:ground`, while each species' responses go on reading it as `ctx.pool.space`; a diagram without outer ports keeps the pool inside the composite, under a private name.

```@example catpd
using Catlab.Programs: @relation

d = @relation (ground,) begin
    grass(ground)
    shrub(ground)
end
on_ground = compose(d, [g, s])
(pool_names(on_ground), advance(on_ground, n, nothing) == advance(meadow2, n, nothing))
```

```@example catpd
closed = compose((@relation () begin
    grass(space)
    shrub(space)
end), [g, s])
(pool_names(closed), pool_names(closed; internal = true))
```

`compose` and `diagram` are methods of Catlab's functions of those names, so loading Catlab alongside this package does not hide them. `advance(c, n, env; rng)` steps a community with demographic stochasticity, and `system(c)` lowers like any pooled system.

## Lowering to MatrixProjectionModels.jl

With MatrixProjectionModels.jl loaded, `lower` turns a pooled system into a `CoupledMPMProblem`. The block below is not run on this page, because these pages are built without that package.

```julia
using MatrixProjectionModels

target = StateDependentMPMTarget(state, (0, 400); p = nothing)
problem = lower(com, target)
solution = solve(problem, DirectIteration())

solution.u[401][:shrub] == out.states[401][:shrub]             # true
solution.substep_log[:pools][1].space == out.pools[1].space    # true
```

The target gives the initial stage vector of each component, under the names of the system's components, and the first and last time step. Its keyword `p` holds the environments: a vector with one environment per time step, or a single value that is used at every step.

In the lowered problem:

- each component is a `PopulationComponent` whose model returns, at each step, the `MatrixProjectionModel` of its net evaluated at the pools of that step, with the transitions marked by `births` kept apart as the fecundity matrix;
- a substep named `:pools` computes the pool totals and the inflows from the state at the start of the step and stores them in the system state, so that `solution.substep_log[:pools]` is the trajectory of the pools;
- each component that has inflows or after-step maps gets one rule, which applies them;
- substeps, rules, events and observables given to the target are kept, and its substeps and rules run after these.

The solution is the one that [`trajectory`](@ref) computes: `solution.u[k]` holds the same stage vectors as `out.states[k]`.

## Lowering to IntegralProjectionModels.jl

When some stages of a net are the mesh cells of a continuous trait, the net can record them as *meshes*: each a name, a `ContinuousDomain` and the cells in the order of their mesh points. This is metadata, carried through `respond`, `⊕`, `expand_stage` and `stratify`, and it does not change the net's matrices. `state_layout` reads the stages of a net as the states of an integral projection model: each mesh whose cells are consecutive is a continuous state, and every other stage a discrete state of its own.

```@docs
meshes
state_layout
```

With IntegralProjectionModels.jl loaded, `lower(com, CoupledIPMTarget(state, (0, 400); p = nothing))` turns a pooled system into a `CoupledIPMProblem`. Each component's model returns, at each step, a `DiscretizedKernel` of its net evaluated at the pools of that step: its survival and fecundity matrices laid out by `state_layout`. The pools, inflows and after-step maps are handled exactly as for a `CoupledMPMProblem`, so the two problems give the same trajectory. With `stochasticity = Demographic()` the inflows are handed to the problem for its demographic mode to draw as Poisson numbers, each component's after its own survival and births.
