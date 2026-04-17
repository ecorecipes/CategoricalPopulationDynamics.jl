"""
Timescale nesting for hierarchical projection models.

Provides `TimescaleEmbedding` and `nest` for composing models that operate
at different timescales (e.g., minutes → days → years). The inner model is
run for a specified number of steps and a summary statistic (eigenvalue,
survival probability, etc.) is extracted to parameterize the outer model.

Categorically, this is operadic composition across a graded timescale
category: each level is a "box" whose output parameterizes transitions
at the next level.

# Example
```julia
# Minute-by-minute foraging → scales daily fecundity
foraging = ValuedProjectionNet([:searching, :handling, :returning],
    :movement => [(:searching => :handling) => 0.02,
                  (:handling => :returning) => 0.1,
                  (:returning => :searching) => 0.2])

colony_base = ValuedProjectionNet([:egg, :larva, :worker, :queen],
    :survival  => [...],
    :fecundity => [(:queen => :egg) => 1.0])  # placeholder

colony = nest(colony_base,
    :fecundity => TimescaleEmbedding(foraging, 480, :lambda))

A = to_matrix(colony)   # runs foraging 480 steps, extracts λ, scales fecundity
```
"""

using LinearAlgebra: eigen, I
using StructuredPopulationCore: lambda

# ---------------------------------------------------------------------------
# Extract functions: how to summarise an inner model's dynamics
# ---------------------------------------------------------------------------

"""
    extract_summary(A::AbstractMatrix, steps::Int, method)

Run projection matrix `A` for `steps` timesteps and extract a scalar summary.

Built-in methods (as `Symbol`):
- `:lambda` — dominant eigenvalue (= `λ(A)^steps`), the per-period growth rate
- `:survival` — mean multi-step survival probability for a substochastic, non-reproductive matrix
- `:throughput` — spectral radius of `A^steps` (= `λ(A)^steps`), same as `:lambda`

Custom methods: pass any `f(A, steps) -> Real`.
"""
function extract_summary(A::AbstractMatrix, steps::Int, method::Symbol)
    if method === :lambda
        λ = lambda(A)
        return λ^steps
    elseif method === :survival
        colsums = vec(sum(A, dims=1))
        tol = 1e-8
        all(c -> -tol <= c <= 1 + tol, colsums) || throw(ArgumentError(
            ":survival requires a substochastic, non-reproductive matrix with column sums in [0, 1]. " *
            "Use a custom extractor for general projection matrices."))

        # Mean column sum of A^steps = mean survival probability
        Ak = A^steps
        return _mean(vec(sum(Ak, dims=1)))
    elseif method === :throughput
        λ = lambda(A)
        return λ^steps
    else
        throw(ArgumentError(
            "Unknown extract method :$method. " *
            "Use :lambda, :survival, :throughput, or pass a function."))
    end
end

function extract_summary(A::AbstractMatrix, steps::Int, f::Function)
    return f(A, steps)
end

# Mean without importing Statistics
function _mean(x)
    s = zero(eltype(x))
    n = 0
    for v in x
        s += v
        n += 1
    end
    return s / n
end

function _finite_or_throw(val::Real, context::AbstractString)
    isfinite(val) || throw(OverflowError(
        "$context produced the non-finite value $val. " *
        "Reduce `steps`, lower `scale`, or use a custom bounded extractor."))
    return val
end

# ---------------------------------------------------------------------------
# TimescaleEmbedding: specification of an inner model + how to summarise it
# ---------------------------------------------------------------------------

"""
    TimescaleEmbedding

Specifies how an inner projection model produces a scalar parameter for
an outer model by running for a fixed number of timesteps and extracting
a summary statistic.

# Fields
- `model` — inner model: `ValuedProjectionNet`, `NestableVPN`, or `AbstractMatrix`
- `steps::Int` — number of inner timesteps per outer timestep
- `extract` — summary method: `:lambda`, `:survival`, `:throughput`, or `f(A, steps) -> Real`
- `scale::Float64` — multiplicative scaling applied to the extracted value (default 1.0)

# Example
```julia
# Foraging model run for 480 minute-steps; extract growth rate
emb = TimescaleEmbedding(foraging_vpn, 480, :lambda)

# Custom: extract fraction of individuals in stage 3 at equilibrium
emb = TimescaleEmbedding(inner_model, 100, (A, steps) -> begin
    v = real.(eigen(A).vectors[:, end])
    v ./= sum(v)
    return v[3]
end)
```
"""
struct TimescaleEmbedding
    model::Any
    steps::Int
    extract::Any       # Symbol or Function
    scale::Real

    function TimescaleEmbedding(model, steps::Int, extract=:lambda; scale::Real=1.0)
        steps > 0 || throw(ArgumentError("steps must be positive, got $steps"))
        isfinite(scale) || throw(ArgumentError("scale must be finite, got $scale"))
        new(model, steps, extract, scale)
    end
end

"""
    evaluate(emb::TimescaleEmbedding) -> Real

Recursively materialize the inner model, run it, and extract the summary.
"""
function evaluate(emb::TimescaleEmbedding)
    A = _materialize(emb.model)
    val = extract_summary(A, emb.steps, emb.extract)
    val isa Real || throw(ArgumentError(
        "Embedding extractor must return a Real, got $(typeof(val))"))
    _finite_or_throw(val, "Embedding extractor $(repr(emb.extract))")

    scaled = emb.scale * val
    scaled isa Real || throw(ArgumentError(
        "Scaled embedding value must be a Real, got $(typeof(scaled))"))
    return _finite_or_throw(scaled, "Embedding scaling")
end

# Dispatch: how to get a matrix from different model types
_materialize(A::AbstractMatrix) = A
_materialize(vnet::ValuedProjectionNet) = to_matrix(vnet)
# NestableVPN handled below after its definition

# ---------------------------------------------------------------------------
# NestableVPN: a VPN where some transitions have embedded inner models
# ---------------------------------------------------------------------------

"""
    NestableVPN

A `ValuedProjectionNet` augmented with `TimescaleEmbedding`s on specific
transitions. When materialized via `to_matrix`, embedded inner models are
recursively evaluated bottom-up, and their extracted summaries scale the
corresponding transition values.

# Fields
- `base::ValuedProjectionNet{T}` — the outer model with placeholder values
- `embeddings::Dict{Symbol, TimescaleEmbedding}` — per-transition embeddings

The embedding **scales** all entries in the named transition by the extracted
value. If the placeholder transition has `(:queen => :egg) => 1.0` and the
embedding evaluates to `λ_inner = 2.5`, the effective value becomes `2.5`.

# Construction
Use `nest` to create:
```julia
nested = nest(base_vpn,
    :fecundity => TimescaleEmbedding(inner, 480, :lambda))
```
"""
struct NestableVPN{T<:Real}
    base::ValuedProjectionNet{T}
    embeddings::Dict{Symbol, TimescaleEmbedding}
end

# Materialize NestableVPN for use inside another embedding
_materialize(nvpn::NestableVPN) = to_matrix(nvpn)

"""
    stage_names(nvpn::NestableVPN)

Return the ordered stage names of the outer model.
"""
stage_names(nvpn::NestableVPN) = stage_names(nvpn.base)

"""
    transition_names(nvpn::NestableVPN)

Return the transition names of the outer model.
"""
transition_names(nvpn::NestableVPN) = transition_names(nvpn.base)

"""
    to_matrix(nvpn::NestableVPN)

Recursively evaluate all embeddings and materialize the full projection matrix.

For each embedded transition, the extracted summary value scales all entries
in that transition. Non-embedded transitions use their base values unchanged.
"""
function to_matrix(nvpn::NestableVPN{T}) where {T}
    n = length(stage_names(nvpn))
    scale_cache = Dict{Symbol, Real}()
    out_type = T

    for (tname, emb) in nvpn.embeddings
        scale = evaluate(emb)
        scale_cache[tname] = scale
        out_type = promote_type(out_type, typeof(scale))
    end

    A = zeros(out_type, n, n)

    for tname in keys(nvpn.base.transition_values)
        M = transition_matrix(nvpn.base, tname)
        if haskey(scale_cache, tname)
            M = M .* scale_cache[tname]
        end
        A .+= M
    end
    return A
end

"""
    transition_matrix(nvpn::NestableVPN, tname::Symbol)

Materialize a single transition, applying its embedding scale if present.
"""
function transition_matrix(nvpn::NestableVPN, tname::Symbol)
    M = transition_matrix(nvpn.base, tname)
    if haskey(nvpn.embeddings, tname)
        scale = evaluate(nvpn.embeddings[tname])
        M = M .* scale
    end
    return M
end

# ---------------------------------------------------------------------------
# nest: the main user-facing constructor
# ---------------------------------------------------------------------------

"""
    nest(vpn::ValuedProjectionNet, pairs::Pair{Symbol, TimescaleEmbedding}...)

Create a `NestableVPN` by attaching `TimescaleEmbedding`s to named transitions.

Each embedding specifies an inner model that is run for N steps; its summary
statistic scales all entries in the corresponding outer transition.

```julia
# Foraging success scales fecundity
colony = nest(colony_base,
    :fecundity => TimescaleEmbedding(foraging, 480, :lambda))

# Multiple embeddings
model = nest(base,
    :fecundity   => TimescaleEmbedding(foraging, 480, :lambda),
    :recruitment => TimescaleEmbedding(dispersal, 24, :survival))
```

Supports recursive nesting — inner models can themselves be `NestableVPN`s:
```julia
population = nest(pop_base,
    :reproduction => TimescaleEmbedding(
        nest(colony_base, :fecundity => TimescaleEmbedding(foraging, 480, :lambda)),
        365, :lambda))
```
"""
function nest(vpn::ValuedProjectionNet{T},
        pairs::Pair{Symbol, TimescaleEmbedding}...) where {T}
    embeddings = Dict{Symbol, TimescaleEmbedding}()
    for (tname, emb) in pairs
        haskey(vpn.transition_values, tname) || throw(ArgumentError(
            "Cannot nest into unknown transition :$tname. " *
            "Available: $(collect(keys(vpn.transition_values)))"))
        embeddings[tname] = emb
    end
    return NestableVPN{T}(vpn, embeddings)
end

"""
    nest(nvpn::NestableVPN, pairs::Pair{Symbol, TimescaleEmbedding}...)

Add additional embeddings to an existing `NestableVPN`.
"""
function nest(nvpn::NestableVPN{T},
        pairs::Pair{Symbol, TimescaleEmbedding}...) where {T}
    new_emb = copy(nvpn.embeddings)
    for (tname, emb) in pairs
        haskey(nvpn.base.transition_values, tname) || throw(ArgumentError(
            "Cannot nest into unknown transition :$tname. " *
            "Available: $(collect(keys(nvpn.base.transition_values)))"))
        new_emb[tname] = emb
    end
    return NestableVPN{T}(nvpn.base, new_emb)
end

# ---------------------------------------------------------------------------
# Integration with ⊕ and ⊘
# ---------------------------------------------------------------------------

"""
    merge(a::NestableVPN, b::ValuedProjectionNet)
    merge(a::ValuedProjectionNet, b::NestableVPN)
    merge(a::NestableVPN, b::NestableVPN)

Merge VPNs preserving any embeddings. Embedding dicts are merged (error on
transition name overlap is already enforced by the base VPN merge).
"""
function Base.merge(a::NestableVPN, b::ValuedProjectionNet)
    merged_base = _merge_two(a.base, b)
    return NestableVPN(merged_base, copy(a.embeddings))
end

function Base.merge(a::ValuedProjectionNet, b::NestableVPN)
    merged_base = _merge_two(a, b.base)
    return NestableVPN(merged_base, copy(b.embeddings))
end

function Base.merge(a::NestableVPN, b::NestableVPN)
    merged_base = _merge_two(a.base, b.base)
    merged_emb = merge(a.embeddings, b.embeddings)
    return NestableVPN(merged_base, merged_emb)
end

# ⊕ operator
⊕(a::NestableVPN, b::ValuedProjectionNet) = Base.merge(a, b)
⊕(a::ValuedProjectionNet, b::NestableVPN) = Base.merge(a, b)
⊕(a::NestableVPN, b::NestableVPN) = Base.merge(a, b)

"""
    map_values(f, nvpn::NestableVPN, tname::Symbol)

Apply `f` to entries in transition `tname`, preserving embeddings.
"""
function map_values(f, nvpn::NestableVPN{T}, tname::Symbol) where {T}
    new_base = map_values(f, nvpn.base, tname)
    return NestableVPN(new_base, copy(nvpn.embeddings))
end

function map_values(f, nvpn::NestableVPN{T}) where {T}
    new_base = map_values(f, nvpn.base)
    return NestableVPN(new_base, copy(nvpn.embeddings))
end

# ⊘ operator
⊘(nvpn::NestableVPN, p::Pair{Symbol, <:Function}) = map_values(p.second, nvpn, p.first)

# ---------------------------------------------------------------------------
# ⋉ operator: unicode sugar for nest
# ---------------------------------------------------------------------------

"""
    vpn ⋉ (:transition => embedding)

Nest an inner model into a transition. Equivalent to `nest(vpn, pair)`.

Type `\\ltimes<TAB>` in the Julia REPL.

```julia
colony = base ⋉ (:fecundity => TimescaleEmbedding(foraging, 480, :lambda))
```

Chain multiple nestings (left-associative, so this works correctly):
```julia
model = base ⋉ (:fecundity => emb1) ⋉ (:recruitment => emb2)
```
"""
⋉(vpn::ValuedProjectionNet, p::Pair{Symbol, TimescaleEmbedding}) = nest(vpn, p)
⋉(nvpn::NestableVPN, p::Pair{Symbol, TimescaleEmbedding}) = nest(nvpn, p)

# ---------------------------------------------------------------------------
# Pretty printing
# ---------------------------------------------------------------------------

function Base.show(io::IO, emb::TimescaleEmbedding)
    print(io, "TimescaleEmbedding(steps=$(emb.steps), extract=$(emb.extract)")
    emb.scale != 1.0 && print(io, ", scale=$(emb.scale)")
    print(io, ")")
end

function Base.show(io::IO, nvpn::NestableVPN{T}) where {T}
    n = length(stage_names(nvpn))
    nt = length(transition_names(nvpn))
    ne = length(nvpn.embeddings)
    print(io, "NestableVPN{$T}($n stages, $nt transitions, $ne embeddings)")
    if ne > 0
        for (k, v) in nvpn.embeddings
            print(io, "\n  :$k ⋉ $(v)")
        end
    end
end
