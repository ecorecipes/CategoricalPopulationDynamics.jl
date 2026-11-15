# Stage Durations & Strata

Two operations refine the stages of a valued projection net and keep its names. `expand_stage` gives a stage a fixed duration: `:egg` becomes the age classes `:egg1`, `:egg2` and `:egg3`, and a new transition moves individuals from each class to the next. `stratify` replicates the whole net across strata, such as infection states or patches: `:larva` becomes `:larva_healthy` and `:larva_infected`, and chosen transitions can move individuals between strata.

Both take a named net and return a named net, so they can be applied one after the other. They also accept the nets described under [Responsive Nets & Pooled Systems](responsive.md), whose responses they carry along.

The method of `stratify` listed here acts on a named net. The methods that act on matrices are under [Stratification & Coarsening](stratification.md).

```@docs
expand_stage
expand_stages
stratify(::ValuedProjectionNet, ::AbstractVector{Symbol})
stratum_stage
stratum_transition
```

## A stage with a fixed duration

```@example catpd
using CategoricalPopulationDynamics

life = ValuedProjectionNet([:egg, :larva, :adult],
    :hatching  => [(:egg => :larva) => 0.5],
    :maturing  => [(:larva => :adult) => 0.4],
    :surviving => [(:adult => :adult) => 0.8],
    :laying    => [(:adult => :egg) => 10.0])

daily = expand_stage(life, :egg, 3; ageing = 0.9)
stage_names(daily)
```

Eggs are now laid into `:egg1` and hatch from `:egg3`. The new transition, `:egg_ageing`, moves a proportion 0.9 of each age class to the next:

```@example catpd
to_matrix(daily)
```

`ageing` may also be a vector with one value per step, and `name` gives the new transition another name. Here the larvae pass through three classes, with 0.7 and then 0.6 moving on:

```@example catpd
growing = expand_stage(life, :larva, 3; ageing = [0.7, 0.6], name = :larval_growth)
transition_matrix(growing, :larval_growth)
```

`expand_stages` expands several stages at once. A stage without an entry in its `ageing` dictionary ages with the value 1.0, as the larvae do here:

```@example catpd
both = expand_stages(life, :egg => 3, :larva => 2; ageing = Dict(:egg => 0.9))
stage_names(both)
```

```@example catpd
to_matrix(both)
```

A stage that keeps individuals in place cannot be given a fixed duration: `expand_stage(life, :adult, 3)` throws an `ArgumentError`, because `:surviving` takes adults to adults. An unknown stage, fewer than two age classes, and a `name` that an existing transition already has are `ArgumentError`s too. An `ageing` vector of the wrong length is a `DimensionMismatch`.

## Strata

```@example catpd
plant = ValuedProjectionNet([:juvenile, :adult],
    :maturing  => [(:juvenile => :adult) => 0.3],
    :surviving => [(:adult => :adult) => 0.5],
    :breeding  => [(:adult => :juvenile) => 2.0])

two = stratify(plant, [:north, :south])
stage_names(two)
```

The stages are listed stratum by stratum, and every transition has one copy in each stratum: `:maturing_north`, `:maturing_south`, and so on. Without a coupling nothing moves between the strata, and the matrix is the one that the matrix method of `stratify` gives with the identity as coupling:

```@example catpd
to_matrix(two) == stratify(to_matrix(plant), [1.0 0.0; 0.0 1.0])
```

`coupling` maps the name of a transition to a matrix over the strata, in which `C[to, from]` is the weight from stratum `from` to stratum `to`. Here a tenth of the young of northern adults settle in the south, and a fifth of the young of southern adults settle in the north:

```@example catpd
D = [0.9 0.2;
     0.1 0.8]
mixed = stratify(plant, [:north, :south]; coupling = Dict(:breeding => D))
sort(transition_names(mixed))
```

```@example catpd
to_matrix(mixed)
```

The two new transitions, `:breeding_north_to_south` and `:breeding_south_to_north`, hold the entries 0.2 and 0.4, and breeding within the two patches falls to 1.8 and 1.6. The matrix is the sum, over the transitions, of the matrix method applied to each transition's own matrix, with the identity for the transitions that have no coupling:

```@example catpd
I2 = [1.0 0.0; 0.0 1.0]
to_matrix(mixed) ≈ stratify(transition_matrix(plant, :maturing), I2) +
                   stratify(transition_matrix(plant, :surviving), I2) +
                   stratify(transition_matrix(plant, :breeding), D)
```

A transition between two strata is added only where the coupling is not zero, so a coupling can be one-way. Below, half of the healthy juveniles that mature join the infected stratum, and nothing comes back from it:

```@example catpd
infection = stratify(plant, [:healthy, :infected];
                     coupling = Dict(:maturing => [0.5 0.0; 0.5 1.0]))
sort(transition_names(infection))
```

`stratum_stage` and `stratum_transition` give the names that `stratify` uses, for a stage, for a transition within a stratum, and for a transition between two strata:

```@example catpd
(stratum_stage(:adult, :infected),
 stratum_transition(:maturing, :healthy),
 stratum_transition(:maturing, :healthy, :infected))
```

## Both together

The two operations can be applied in either order. A duration given first is repeated in every stratum:

```@example catpd
stage_names(stratify(expand_stage(plant, :juvenile, 2), [:north, :south]))
```

Strata made first can be refined one at a time:

```@example catpd
stage_names(expand_stage(stratify(plant, [:north, :south]), :juvenile_south, 2))
```
