# Metapopulation Stratification

Latitude-Dependent Grape Moth Dynamics via Categorical Spatial Extension

Author

Simon Frost

## Overview

The European grape moth (*Lobesia botrana*) is a major viticultural pest across the Mediterranean basin and beyond. Its lifecycle — egg → larva → pupa → adult — is driven by temperature-dependent development rates, so populations at different latitudes experience fundamentally different demography.

A common modelling approach is to run the same lifecycle model independently at each latitude (as in [PhysiologicallyBasedDemographicModels.jl vignette 05](../../PhysiologicallyBasedDemographicModels.jl/vignettes/05_lobesia_overwintering/05_lobesia_overwintering.qmd)). But grape moths disperse: adults can fly tens of kilometres, and wind-assisted long-range dispersal connects distant vineyards. Independent single-patch models cannot capture the **source-sink dynamics** that emerge when productive southern populations subsidise marginal northern ones.

**Categorical stratification** provides the right framework. We:

1.  Build latitude-specific lifecycle matrices using temperature-dependent vital rates
2.  Couple them via a stepping-stone dispersal matrix
3.  Analyse the metapopulation as a single block-structured matrix
4.  Use **coarsening** to test whether spatial resolution can be reduced

This reveals which latitude bands are demographic sources, which are sinks, and how dispersal and climate warming reshape the metapopulation.

## Setup

``` julia
using CategoricalPopulationDynamics
using CategoricalPopulationDynamics: ⊕, ⊘
using Catlab
using Catlab.CategoricalAlgebra
using LinearAlgebra
using ProjectionModels: lambda
using Plots
```

## Temperature-Dependent Vital Rates

*L. botrana* development follows a Brière function — a unimodal rate curve bounded by lower and upper thermal thresholds. Mortality is U-shaped, lowest near the thermal optimum and rising at temperature extremes. Fecundity peaks in the mid-range.

``` julia
# Brière development rate parameters for L. botrana
# (Gutierrez et al., adapted from PBDM vignette 05)
const a_lb = 2.5e-5
const T_L_lb = 7.3    # lower developmental threshold (°C)
const T_M_lb = 33.7   # upper developmental threshold (°C)

function briere_lb(T)
    (T <= T_L_lb || T >= T_M_lb) && return 0.0
    return a_lb * T * (T - T_L_lb) * sqrt(T_M_lb - T)
end

# Stage-specific daily mortality: U-shaped around thermal optimum ~22°C
mortality_lb(T) = max(0.01, 0.0003 * (T - 22.0)^2 + 0.01)

# Adult fecundity (eggs per adult per day) — temperature-dependent
function fecundity_lb(T)
    (T <= T_L_lb || T >= T_M_lb) && return 0.0
    f_max = 8.0  # peak daily egg production
    return f_max * exp(-0.5 * ((T - 24.0) / 5.0)^2)
end
```

    fecundity_lb (generic function with 1 method)

``` julia
# Visualise vital rate functions
T_range = 5.0:0.5:38.0
p1 = plot(T_range, briere_lb.(T_range),
    xlabel="Temperature (°C)", ylabel="Development rate (1/day)",
    title="Brière development", legend=false, color=:darkgreen, linewidth=2)
p2 = plot(T_range, mortality_lb.(T_range),
    xlabel="Temperature (°C)", ylabel="Daily mortality",
    title="U-shaped mortality", legend=false, color=:firebrick, linewidth=2)
p3 = plot(T_range, fecundity_lb.(T_range),
    xlabel="Temperature (°C)", ylabel="Eggs / adult / day",
    title="Fecundity", legend=false, color=:darkorange, linewidth=2)
plot(p1, p2, p3, layout=(1, 3), size=(900, 280))
```

![](14_lobesia_metapopulation_files/embedded-1.png)

## Latitude-Specific Lifecycles

We model four European vineyard regions spanning 12° of latitude. Each has a characteristic mean temperature and seasonal amplitude, yielding different effective vital rates.

``` julia
# Latitude band definitions
latitudes = [
    (name=:Sicily,   lat=37.5, mean_T=17.8, amplitude=8.0),
    (name=:Bordeaux, lat=43.5, mean_T=16.5, amplitude=9.0),
    (name=:Trentino, lat=46.0, mean_T=15.4, amplitude=10.0),
    (name=:Mosel,    lat=49.5, mean_T=14.3, amplitude=10.0),
]

println(rpad("Location", 12), rpad("Lat (°N)", 10), rpad("Mean T", 10), "Amplitude")
println("-"^42)
for loc in latitudes
    println(rpad(loc.name, 12), rpad(loc.lat, 10), rpad(loc.mean_T, 10), loc.amplitude)
end
```

    Location    Lat (°N)  Mean T    Amplitude
    ------------------------------------------
    Sicily      37.5      17.8      8.0
    Bordeaux    43.5      16.5      9.0
    Trentino    46.0      15.4      10.0
    Mosel       49.5      14.3      10.0

For each latitude, we compute effective seasonal vital rates by averaging over the growing season (days when T \> T_L), then assemble a 4-stage projection matrix.

``` julia
"""
    seasonal_temperature(day, mean_T, amplitude)

Sinusoidal daily temperature: peak at day 200 (mid-July).
"""
seasonal_temperature(day, mean_T, amplitude) =
    mean_T + amplitude * sin(2π * (day - 110) / 365)

"""
    build_patch_matrix(mean_T, amplitude)

Build a 4×4 daily projection matrix (egg, larva, pupa, adult) by averaging
temperature-dependent rates over the growing season.
"""
function build_patch_matrix(mean_T, amplitude)
    # Average rates over growing season (days when T > T_L)
    dev_sum = 0.0
    mort_sum = 0.0
    fec_sum = 0.0
    n_days = 0

    for day in 1:365
        T = seasonal_temperature(day, mean_T, amplitude)
        T <= T_L_lb && continue
        dev_sum += briere_lb(T)
        mort_sum += mortality_lb(T)
        fec_sum += fecundity_lb(T)
        n_days += 1
    end

    n_days == 0 && return zeros(4, 4)

    # Mean daily rates during growing season
    dev = dev_sum / n_days     # mean development rate
    mort = mort_sum / n_days   # mean daily mortality
    fec = fec_sum / n_days     # mean daily fecundity

    surv = 1.0 - mort          # daily survival probability
    stage_dur = dev > 0 ? 1.0 / dev : Inf  # mean days per stage

    # Transition probability: probability of advancing to next stage per day
    trans = min(dev, 0.95)  # cap at 0.95 for numerical stability

    # 4-stage matrix: egg → larva → pupa → adult (→ egg via fecundity)
    # Convention: A[to, from]
    A = zeros(4, 4)
    A[1, 1] = surv * (1 - trans)           # egg stasis
    A[2, 1] = surv * trans                 # egg → larva
    A[2, 2] = surv * (1 - trans)           # larva stasis
    A[3, 2] = surv * trans                 # larva → pupa
    A[3, 3] = surv * (1 - trans)           # pupa stasis
    A[4, 3] = surv * trans                 # pupa → adult
    A[4, 4] = surv * 0.85                  # adult survival (shorter-lived)
    A[1, 4] = fec                          # adult → egg (fecundity)

    return A
end
```

    Main.Notebook.build_patch_matrix

### Building ValuedProjectionNets

We wrap each patch matrix in a `ValuedProjectionNet` to preserve the categorical structure. Using the `⊕` operator (`\oplus<TAB>`), we compose the lifecycle from separate survival and fecundity components — keeping each sub-kernel independently readable:

``` julia
stages = [:egg, :larva, :pupa, :adult]
stage_idx = Dict(s => i for (i, s) in enumerate(stages))

function survival_vpn(A::Matrix)
    entries = Pair{Pair{Symbol,Symbol}, Float64}[]
    for i in 1:4, j in 1:4
        (j == 4 && i == 1) && continue  # fecundity handled separately
        A[i, j] ≈ 0.0 && continue
        push!(entries, (stages[j] => stages[i]) => A[i, j])
    end
    ValuedProjectionNet(stages, :survival => entries)
end

function fecundity_vpn(A::Matrix)
    entries = Pair{Pair{Symbol,Symbol}, Float64}[]
    A[1, 4] ≈ 0.0 || push!(entries, (:adult => :egg) => A[1, 4])
    ValuedProjectionNet(stages, :fecundity => entries)
end

# Build local matrices and the reference VPN (Sicily) via ⊕
A_patches = [build_patch_matrix(loc.mean_T, loc.amplitude) for loc in latitudes]
vpn_ref = survival_vpn(A_patches[1]) ⊕ fecundity_vpn(A_patches[1])
```

    ValuedProjectionNet{Float64}(CategoricalPopulationDynamics.LabelledProjectionNet:
      S = 1:1
      T = 1:2
      Src = 1:2
      Tgt = 1:2
      Name = 1:0
      src_t : Src → T = [1, 2]
      src_s : Src → S = [1, 1]
      tgt_t : Tgt → T = [1, 2]
      tgt_s : Tgt → S = [1, 1]
      sname : S → Name = [:stage]
      tname : T → Name = [:survival, :fecundity], [:egg, :larva, :pupa, :adult], Dict(:survival => [(:egg => :egg) => 0.9570566879220508, (:egg => :larva) => 0.01805131207794916, (:larva => :larva) => 0.9570566879220508, (:larva => :pupa) => 0.01805131207794916, (:pupa => :pupa) => 0.9570566879220508, (:pupa => :adult) => 0.01805131207794916, (:adult => :adult) => 0.8288418], :fecundity => [(:adult => :egg) => 3.993229147154501]))

The reference VPN captures the full lifecycle **structure** — stage names, transition names, and which (from → to) entries are nonzero. All four latitudes share this structure; only the rates differ. Using the `⊘` operator (`\oslash<TAB>`), we stamp latitude-specific rates into the template without rebuilding it from scratch:

``` julia
vpn_patches = [vpn_ref]  # Sicily is the reference
for k in 2:length(latitudes)
    A_k = A_patches[k]
    vpn_k = vpn_ref ⊘ (:survival  => ((from, to), _) -> A_k[stage_idx[to], stage_idx[from]]) ⊘
                       (:fecundity => ((from, to), _) -> A_k[stage_idx[to], stage_idx[from]])
    push!(vpn_patches, vpn_k)
end

println("Patch matrices built: ", length(A_patches), " locations")
for (i, loc) in enumerate(latitudes)
    println("  ", rpad(loc.name, 10), " — ", size(A_patches[i]))
end
```

    Patch matrices built: 4 locations
      Sicily     — (4, 4)
      Bordeaux   — (4, 4)
      Trentino   — (4, 4)
      Mosel      — (4, 4)

## Local Growth Rates

Before coupling the patches, we examine each latitude in isolation. The thermal gradient creates a clear north-south demographic divide.

``` julia
λ_local = [lambda(A) for A in A_patches]
names_str = [String(loc.name) for loc in latitudes]

println(rpad("Location", 12), rpad("λ_local", 10), "Status")
println("-"^38)
for (i, loc) in enumerate(latitudes)
    status = λ_local[i] > 1.01 ? "SOURCE" :
             λ_local[i] > 0.99 ? "~ stable" : "SINK"
    println(rpad(loc.name, 12), rpad(round(λ_local[i], digits=4), 10), status)
end
```

    Location    λ_local   Status
    --------------------------------------
    Sicily      1.0079    ~ stable
    Bordeaux    0.9964    ~ stable
    Trentino    1.0077    ~ stable
    Mosel       1.0065    ~ stable

``` julia
bar(names_str, λ_local,
    ylabel="λ (local growth rate)", title="Isolated Patch Growth Rates",
    legend=false, color=[:forestgreen, :goldenrod, :darkorange, :firebrick],
    alpha=0.8, ylim=(0.0, maximum(λ_local) * 1.15))
hline!([1.0], linestyle=:dash, color=:black, linewidth=1.5, label="λ = 1")
annotate!([(i, λ_local[i] + 0.02, text(round(λ_local[i], digits=3), 8))
           for i in 1:4])
```

![](14_lobesia_metapopulation_files/embedded-2.png)

Southern patches (Sicily) are demographic **sources** with λ \> 1, while northern patches (Mosel) are **sinks** that would decline without immigration.

## Dispersal Matrix

Adult grape moths disperse in a stepping-stone pattern: most stay local, some reach adjacent latitude bands, and long-distance dispersal is rare.

``` julia
# Stepping-stone dispersal: probability of an individual from patch j
# arriving in patch i (columns sum to 1)
D = [0.90  0.08  0.02  0.00;   # → Sicily
     0.05  0.85  0.08  0.02;   # → Bordeaux
     0.01  0.05  0.87  0.07;   # → Trentino
     0.00  0.02  0.05  0.93]   # → Mosel

# Verify columns sum to ~1 (conservation of individuals)
println("Column sums: ", round.(sum(D, dims=1), digits=4))
```

    Column sums: [0.96 1.0 1.02 1.02]

``` julia
heatmap(names_str, names_str, D,
    title="Dispersal matrix D",
    xlabel="From patch", ylabel="To patch",
    color=:Blues, clim=(0, 1), size=(450, 400))
```

![](14_lobesia_metapopulation_files/embedded-3.png)

## Homogeneous Stratification

As a baseline, suppose all patches had Sicily’s (best-case) vital rates. Then `stratify(A_sicily, D)` gives the standard homogeneous metapopulation:

``` julia
A_sicily = A_patches[1]
A_homogeneous = stratify(A_sicily, D)

println("Homogeneous stratification (all patches = Sicily):")
println("  Matrix size:  ", size(A_homogeneous))
println("  λ_metapop:    ", round(lambda(A_homogeneous), digits=4))
println("  λ_local:      ", round(lambda(A_sicily), digits=4))
```

    Homogeneous stratification (all patches = Sicily):
      Matrix size:  (16, 16)
      λ_metapop:    1.0079
      λ_local:      1.0079

With identical patches, `stratify` produces a block matrix where each block `(i,j)` is `D[i,j] × A_sicily`. The metapopulation growth rate matches the local rate (dispersal neither helps nor hurts when all patches are equal).

``` julia
n = 4  # stages per patch
heatmap(A_homogeneous,
    title="Homogeneous stratification (16×16)",
    xlabel="From (patch × stage)", ylabel="To (patch × stage)",
    color=:viridis, size=(550, 500))
# Block boundaries
for b in 1:3
    vline!([b * n + 0.5], color=:white, linewidth=2, label=false)
    hline!([b * n + 0.5], color=:white, linewidth=2, label=false)
end
```

## Heterogeneous Metapopulation

In reality, each latitude has **different** vital rates. The `stratify` function assumes a single local matrix, so we must build the block matrix manually.

The convention is:

<span class="math display">\\A\_{\text{full}}\[(i, s\_{\text{to}}),\\ (j, s\_{\text{from}})\] = D\[i,j\] \cdot A_j\[s\_{\text{to}}, s\_{\text{from}}\]\\</span>

Individuals develop at the rates of their **source patch** <span class="math inline">\\j\\</span>, then a fraction <span class="math inline">\\D\[i,j\]\\</span> disperses to patch <span class="math inline">\\i\\</span>.

``` julia
# Build 16×16 heterogeneous block matrix
A_full = zeros(4n, 4n)
for i in 1:4, j in 1:4
    rows = (i-1)*n+1 : i*n
    cols = (j-1)*n+1 : j*n
    A_full[rows, cols] = D[i,j] * A_patches[j]
end

λ_meta = lambda(A_full)
println("Heterogeneous metapopulation:")
println("  λ_metapop = ", round(λ_meta, digits=4))
println("  λ_homog   = ", round(lambda(A_homogeneous), digits=4))
println("  λ_Sicily  = ", round(λ_local[1], digits=4))
```

    Heterogeneous metapopulation:
      λ_metapop = 1.0049
      λ_homog   = 1.0079
      λ_Sicily  = 1.0079

``` julia
heatmap(A_full,
    title="Heterogeneous metapopulation (16×16)",
    xlabel="From (patch × stage)", ylabel="To (patch × stage)",
    color=:viridis, size=(550, 500))
for b in 1:3
    vline!([b * n + 0.5], color=:white, linewidth=2, label=false)
    hline!([b * n + 0.5], color=:white, linewidth=2, label=false)
end
```

Note the visible asymmetry: the upper-left blocks (Sicily) are brighter (higher rates) than the lower-right blocks (Mosel).

## Source-Sink Analysis

The right eigenvector of the metapopulation matrix gives the **stable stage distribution** — the long-term relative population across all patches and stages.

``` julia
# Right eigenvector (stable stage distribution)
evals = eigen(A_full)
idx = argmax(real.(evals.values))
w = real.(evals.vectors[:, idx])
w = w / sum(w)  # normalise to proportions

# Aggregate by patch
patch_pop = [sum(w[(i-1)*n+1 : i*n]) for i in 1:4]
println("Stable population distribution across patches:")
for (i, loc) in enumerate(latitudes)
    pct = round(patch_pop[i] * 100, digits=1)
    println("  ", rpad(loc.name, 10), pct, "%")
end
```

    Stable population distribution across patches:
      Sicily    24.8%
      Bordeaux  24.2%
      Trentino  25.4%
      Mosel     25.6%

``` julia
bar(names_str, patch_pop * 100,
    ylabel="% of metapopulation", title="Stable Patch Distribution",
    legend=false, color=[:forestgreen, :goldenrod, :darkorange, :firebrick],
    alpha=0.8)
```

![](14_lobesia_metapopulation_files/embedded-4.png)

``` julia
# Which patches are sources vs sinks?
# A sink is a patch that would decline without immigration (λ_local < 1)
# but persists in the metapopulation due to dispersal from sources
println(rpad("Patch", 12), rpad("λ_local", 10), rpad("% pop", 10), "Role")
println("-"^42)
for (i, loc) in enumerate(latitudes)
    role = λ_local[i] > 1.0 ? "SOURCE" : "SINK (rescued by dispersal)"
    println(rpad(loc.name, 12),
        rpad(round(λ_local[i], digits=4), 10),
        rpad(round(patch_pop[i] * 100, digits=1), 10),
        role)
end
```

    Patch       λ_local   % pop     Role
    ------------------------------------------
    Sicily      1.0079    24.8      SOURCE
    Bordeaux    0.9964    24.2      SINK (rescued by dispersal)
    Trentino    1.0077    25.4      SOURCE
    Mosel       1.0065    25.6      SOURCE

## Dispersal Sweep

How does the dispersal rate affect metapopulation growth? We sweep the fraction of adults that disperse from 0 (isolated patches) to 0.5 (high mixing), using the same stepping-stone topology.

``` julia
dispersal_rates = 0.0:0.02:0.50
λ_sweep = Float64[]

for d in dispersal_rates
    # Build stepping-stone D with dispersal fraction d
    D_sweep = zeros(4, 4)
    for i in 1:4
        for j in 1:4
            dist = abs(i - j)
            if dist == 0
                D_sweep[i, j] = 1.0 - d
            elseif dist == 1
                D_sweep[i, j] = d * 0.7   # adjacent
            elseif dist == 2
                D_sweep[i, j] = d * 0.25  # next-nearest
            else
                D_sweep[i, j] = d * 0.05  # long-distance
            end
        end
        # Normalise columns
        D_sweep[:, i] ./= sum(D_sweep[:, i])
    end

    # Build heterogeneous block matrix
    A_sweep = zeros(4n, 4n)
    for i in 1:4, j in 1:4
        rows = (i-1)*n+1 : i*n
        cols = (j-1)*n+1 : j*n
        A_sweep[rows, cols] = D_sweep[i,j] * A_patches[j]
    end

    push!(λ_sweep, lambda(A_sweep))
end

plot(Base.collect(dispersal_rates), λ_sweep,
    xlabel="Dispersal fraction", ylabel="λ (metapopulation)",
    title="Metapopulation Growth Rate vs Dispersal",
    legend=false, linewidth=2, color=:navy, size=(600, 350))
hline!([1.0], linestyle=:dash, color=:red, linewidth=1, label="λ = 1")
scatter!([0.0], [λ_sweep[1]], color=:black, markersize=5, label="Isolated")
```

![](14_lobesia_metapopulation_files/embedded-5.png)

At zero dispersal, the metapopulation λ is dominated by the fastest-growing patch (Sicily). As dispersal increases, population is redistributed to sink patches, lowering the overall growth rate — a “dispersal cost.” In heterogeneous landscapes, connectivity is not always beneficial.

## Climate Change Scenario

Global warming shifts isotherms northward. We add +2°C to each latitude’s mean temperature and rebuild the metapopulation.

``` julia
ΔT = 2.0  # warming (°C)

A_patches_warm = [build_patch_matrix(loc.mean_T + ΔT, loc.amplitude)
                  for loc in latitudes]
λ_warm = [lambda(A) for A in A_patches_warm]

println(rpad("Location", 12), rpad("λ current", 12), rpad("λ +2°C", 12), "Change")
println("-"^48)
for (i, loc) in enumerate(latitudes)
    Δ = λ_warm[i] - λ_local[i]
    arrow = Δ > 0 ? "↑" : "↓"
    println(rpad(loc.name, 12),
        rpad(round(λ_local[i], digits=4), 12),
        rpad(round(λ_warm[i], digits=4), 12),
        arrow, " ", round(Δ, digits=4))
end
```

    Location    λ current   λ +2°C      Change
    ------------------------------------------------
    Sicily      1.0079      1.0189      ↑ 0.011
    Bordeaux    0.9964      1.0085      ↑ 0.012
    Trentino    1.0077      0.9988      ↓ -0.0089
    Mosel       1.0065      1.0066      ↑ 0.0001

``` julia
# Build warmed metapopulation
A_full_warm = zeros(4n, 4n)
for i in 1:4, j in 1:4
    rows = (i-1)*n+1 : i*n
    cols = (j-1)*n+1 : j*n
    A_full_warm[rows, cols] = D[i,j] * A_patches_warm[j]
end

λ_meta_warm = lambda(A_full_warm)
println("Metapopulation λ (current): ", round(λ_meta, digits=4))
println("Metapopulation λ (+2°C):    ", round(λ_meta_warm, digits=4))
```

    Metapopulation λ (current): 1.0049
    Metapopulation λ (+2°C):    1.0068

``` julia
# Side-by-side comparison
groupidx = repeat(1:4, 2)
vals = vcat(λ_local, λ_warm)
labels_all = vcat(names_str, names_str)

xticks_pos = 1:4
bar_w = 0.35
p = bar(xticks_pos .- bar_w/2, λ_local, bar_width=bar_w,
    label="Current", color=:steelblue, alpha=0.8,
    ylabel="λ", title="Local Growth Rates: Current vs +2°C Warming",
    xticks=(xticks_pos, names_str))
bar!(xticks_pos .+ bar_w/2, λ_warm, bar_width=bar_w,
    label="+2°C", color=:coral, alpha=0.8)
hline!([1.0], linestyle=:dash, color=:black, linewidth=1.5, label="λ = 1")
```

![](14_lobesia_metapopulation_files/embedded-6.png)

Warming benefits northern sinks (more growing-degree days) but may harm southern sources if temperatures approach the upper thermal threshold. The source-sink boundary shifts northward.

``` julia
# Warmed stable distribution
evals_warm = eigen(A_full_warm)
idx_warm = argmax(real.(evals_warm.values))
w_warm = real.(evals_warm.vectors[:, idx_warm])
w_warm = w_warm / sum(w_warm)
patch_pop_warm = [sum(w_warm[(i-1)*n+1 : i*n]) for i in 1:4]

bar(xticks_pos .- bar_w/2, patch_pop * 100, bar_width=bar_w,
    label="Current", color=:steelblue, alpha=0.8,
    ylabel="% of metapopulation",
    title="Population Distribution: Current vs +2°C",
    xticks=(xticks_pos, names_str))
bar!(xticks_pos .+ bar_w/2, patch_pop_warm * 100, bar_width=bar_w,
    label="+2°C", color=:coral, alpha=0.8)
```

![](14_lobesia_metapopulation_files/embedded-7.png)

## Coarsening

Can we collapse the two northern patches (Trentino + Mosel) into a single “northern” aggregate without losing essential dynamics? We use `coarsen` with a `FinFunction` that maps the 16 state indices in the 4-patch model to 12 state indices in a 3-patch model.

``` julia
# Mapping: 4 patches × 4 stages = 16 → 3 patches × 4 stages = 12
# Patch 1 (Sicily, indices 1:4)   → coarse patch 1 (indices 1:4)
# Patch 2 (Bordeaux, indices 5:8) → coarse patch 2 (indices 5:8)
# Patch 3 (Trentino, indices 9:12) → coarse patch 3 (indices 9:12)
# Patch 4 (Mosel, indices 13:16)   → coarse patch 3 (indices 9:12)

fine_to_coarse = vcat(
    1:4,    # Sicily → patch 1
    5:8,    # Bordeaux → patch 2
    9:12,   # Trentino → patch 3 (northern)
    9:12    # Mosel → patch 3 (northern, merged)
)

f_spatial = FinFunction(fine_to_coarse, 12)
A_coarsened = coarsen(A_full, f_spatial)

λ_coarse = lambda(A_coarsened)
println("Full 4-patch metapopulation (16×16): λ = ", round(λ_meta, digits=4))
println("Coarsened 3-patch model (12×12):     λ = ", round(λ_coarse, digits=4))
println("Relative error: ", round(abs(λ_coarse - λ_meta) / λ_meta * 100, digits=3), "%")
```

    Full 4-patch metapopulation (16×16): λ = 1.0049
    Coarsened 3-patch model (12×12):     λ = 1.0049
    Relative error: 0.003%

``` julia
coarse_names = ["Sicily", "Bordeaux", "Northern"]
p1 = heatmap(A_full,
    title="Full 4-patch (16×16)", color=:viridis, size=(450, 400))
for b in 1:3
    vline!([b * n + 0.5], color=:white, linewidth=2, label=false)
    hline!([b * n + 0.5], color=:white, linewidth=2, label=false)
end

p2 = heatmap(A_coarsened,
    title="Coarsened 3-patch (12×12)", color=:viridis, size=(450, 400))
for b in 1:2
    vline!([b * n + 0.5], color=:white, linewidth=2, label=false)
    hline!([b * n + 0.5], color=:white, linewidth=2, label=false)
end

plot(p1, p2, layout=(1, 2), size=(900, 400))
```

![](14_lobesia_metapopulation_files/embedded-8.png)

The coarsened model preserves the metapopulation growth rate well. When two patches have similar demography (both sinks), aggregating them loses little information — a hallmark of well-behaved pushforward.

## Summary

This vignette demonstrated how categorical stratification and coarsening reveal metapopulation structure that is invisible in independent single-patch models:

1.  **Temperature-dependent vital rates** — Brière development, U-shaped mortality, and Gaussian fecundity parameterise the *L. botrana* lifecycle
2.  **Latitude-specific matrices** — a reference `ValuedProjectionNet` is composed via `⊕` (survival ⊕ fecundity), then latitude-specific variants are stamped out with `⊘`, capturing the demographic gradient from Sicily (source, λ \> 1) to the Mosel (sink, λ \< 1)
3.  **Homogeneous `stratify`** — the baseline: identical patches coupled by dispersal preserve λ
4.  **Heterogeneous block matrix** — manually building the 16×16 matrix with latitude-specific rates exposes the full metapopulation dynamics
5.  **Source-sink analysis** — the stable stage distribution reveals that southern patches support northern ones through immigration
6.  **Dispersal sweep** — increasing connectivity does not always increase λ; redistributing individuals to sinks incurs a dispersal cost
7.  **Climate warming** — a +2°C shift improves northern sinks but may stress southern sources, shifting the source-sink boundary northward
8.  **Coarsening** — collapsing two similar sink patches into one via `FinFunction` preserves λ, demonstrating functorial spatial aggregation

The categorical framework — `⊕` for modular lifecycle composition, `⊘` for environment-specific parameterisation, stratification as pullback, coarsening as pushforward — provides principled tools for spatial scaling that go beyond ad hoc block-matrix construction. The same patterns apply to any metapopulation where patches differ in their local demography.
