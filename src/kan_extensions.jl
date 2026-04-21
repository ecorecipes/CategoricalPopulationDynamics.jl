"""
Kan extension functors between kernel spaces and matrix spaces.

- **Left Kan extension** (Lan_D): kernel → matrix (discretisation)
- **Right Kan extension** (Ran_D): matrix → piecewise-constant kernel (refinement)

These form the adjunction chain: Lan_D ⊣ D* ⊣ Ran_D

## Quadrature Rules

Three quadrature rules are supported, corresponding to formal results in the
Lean formalization (`kan_markov_bridge`):

- `:midpoint` — `A[i,j] = h·K(zᵢ,zⱼ)`, error O(h²) with coefficient M₂/24
- `:trapezoidal` — endpoint-average weighting, error O(h²) with coefficient M₂/12
- `:simpson` — `(K(a,·) + 4K(m,·) + K(b,·))/6`, error O(h⁴) with coefficient M₄/720

**Note on stochastic kernels:** Higher-order rules (especially Simpson's) can
produce negative matrix entries for non-smooth kernels. Use `ensure_nonneg=true`
to clamp negative values and `normalize_rows=true` to restore row-sum structure
when constructing Markov transition matrices.
"""

# ---------------------------------------------------------------------------
# Quadrature rule enum
# ---------------------------------------------------------------------------

"""
    QuadratureRule

Quadrature rule for kernel discretisation.

- `Midpoint()` — O(h²), coefficient M₂/24 (Lean: Part 5, Result 15)
- `Trapezoidal()` — O(h²), coefficient M₂/12 (Lean: Part 9, Results 31–33)
- `Simpson()` — O(h⁴), coefficient M₄/720 (Lean: Part 14, Results 58–72)
"""
abstract type QuadratureRule end
struct Midpoint <: QuadratureRule end
struct Trapezoidal <: QuadratureRule end
struct Simpson <: QuadratureRule end

"""
    theoretical_error_order(::QuadratureRule)

Return the convergence order of the quadrature rule.
"""
theoretical_error_order(::Midpoint) = 2
theoretical_error_order(::Trapezoidal) = 2
theoretical_error_order(::Simpson) = 4

"""
    theoretical_error_coefficient(::QuadratureRule)

Return the leading error coefficient (numerator/denominator of M_k·h^p bound).
"""
theoretical_error_coefficient(::Midpoint) = (1, 24)    # M₂·h²/24
theoretical_error_coefficient(::Trapezoidal) = (1, 12) # M₂·h²/12
theoretical_error_coefficient(::Simpson) = (1, 720)    # M₄·h⁴/720

# ---------------------------------------------------------------------------
# Left Kan extension (discretisation)
# ---------------------------------------------------------------------------

"""
    left_kan_extension(kernel_fn, domain; rule=:midpoint, ensure_nonneg=false, normalize_rows=false)

Discretise a continuous kernel `kernel_fn(z_new, z)` into a matrix.

## Quadrature rules

- `:midpoint` (default) — `A[i,j] = h·K(zᵢ, zⱼ)` where zᵢ are bin midpoints.
  Error O(h²) with coefficient M₂/24. (Lean: `midpoint_quadrature_error`)
- `:trapezoidal` — averages kernel values at bin endpoints.
  Error O(h²) with coefficient M₂/12. (Lean: `trapezoidal_approximates_binAverage`)
- `:simpson` — weighted combination: `(K(aᵢ,·) + 4K(mᵢ,·) + K(bᵢ,·))/6`.
  Error O(h⁴) with coefficient M₄/720. (Lean: `simpsonAverage_eq_weighted`)

## Positivity options

- `ensure_nonneg=true`: clamp negative entries to zero (Simpson can produce negatives)
- `normalize_rows=true`: rescale each row so entries sum to the original row sum

These options are essential when constructing Markov transition matrices where
positivity and row-sum structure must be preserved.
"""
function left_kan_extension(kernel_fn, domain::ContinuousProjectionDomain;
                            rule::Symbol=:midpoint,
                            ensure_nonneg::Bool=false,
                            normalize_rows::Bool=false)
    A = if rule == :midpoint
        _midpoint_discretise(kernel_fn, domain)
    elseif rule == :trapezoidal
        _trapezoidal_discretise(kernel_fn, domain)
    elseif rule == :simpson
        _simpson_discretise(kernel_fn, domain)
    else
        throw(ArgumentError("Unknown quadrature rule: $rule. Use :midpoint, :trapezoidal, or :simpson."))
    end
    _postprocess!(A; ensure_nonneg, normalize_rows)
    return A
end

function left_kan_extension(kernel_fn, domain::ContinuousDomain; kwargs...)
    cpd = ContinuousProjectionDomain(domain.lower, domain.upper, domain.n_meshpoints)
    return left_kan_extension(kernel_fn, cpd; kwargs...)
end

# ---------------------------------------------------------------------------
# Internal: midpoint rule (original implementation)
# ---------------------------------------------------------------------------

"""Midpoint rule: A[i,j] = h · K(zᵢ, zⱼ)"""
function _midpoint_discretise(kernel_fn, domain::ContinuousProjectionDomain)
    z = meshpoints(domain)
    h = step_size(domain)
    m = length(z)
    A = zeros(m, m)
    @inbounds for j in 1:m
        for i in 1:m
            A[i, j] = h * kernel_fn(z[i], z[j])
        end
    end
    return A
end

# ---------------------------------------------------------------------------
# Internal: trapezoidal rule
#
# Lean reference: TrapezoidalRule.lean
# trapezoidalAverage(f, I) = (f(I.a) + f(I.b)) / 2
#
# For a 2D kernel K(z',z), integrate over the source bin [aⱼ, bⱼ]:
#   ∫ K(zᵢ', z) dz ≈ h · (K(zᵢ', aⱼ) + K(zᵢ', bⱼ)) / 2
# where zᵢ' is the midpoint of the target bin.
# ---------------------------------------------------------------------------

"""Trapezoidal rule: A[i,j] = h · (K(zᵢ, aⱼ) + K(zᵢ, bⱼ)) / 2"""
function _trapezoidal_discretise(kernel_fn, domain::ContinuousProjectionDomain)
    z = meshpoints(domain)
    edges = bounds(domain)
    h = step_size(domain)
    m = length(z)
    A = zeros(m, m)
    @inbounds for j in 1:m
        aj, bj = edges[j], edges[j + 1]
        for i in 1:m
            A[i, j] = h * (kernel_fn(z[i], aj) + kernel_fn(z[i], bj)) / 2
        end
    end
    return A
end

# ---------------------------------------------------------------------------
# Internal: Simpson's rule
#
# Lean reference: SimpsonRule.lean
# simpsonAverage(f, I) = (f(I.a) + 4·f(I.midpoint) + f(I.b)) / 6
# Proven: simpsonAverage = 2/3·midpoint + 1/3·trapezoidal
#
# For a 2D kernel, integrate over source bin [aⱼ, bⱼ]:
#   ∫ K(zᵢ', z) dz ≈ h · (K(zᵢ', aⱼ) + 4·K(zᵢ', mⱼ) + K(zᵢ', bⱼ)) / 6
# ---------------------------------------------------------------------------

"""Simpson's rule: A[i,j] = h · (K(zᵢ, aⱼ) + 4K(zᵢ, mⱼ) + K(zᵢ, bⱼ)) / 6"""
function _simpson_discretise(kernel_fn, domain::ContinuousProjectionDomain)
    z = meshpoints(domain)  # midpoints mⱼ of each bin
    edges = bounds(domain)
    h = step_size(domain)
    m = length(z)
    A = zeros(m, m)
    @inbounds for j in 1:m
        aj, bj = edges[j], edges[j + 1]
        mj = z[j]  # midpoint = meshpoint
        for i in 1:m
            A[i, j] = h * (kernel_fn(z[i], aj) + 4 * kernel_fn(z[i], mj) + kernel_fn(z[i], bj)) / 6
        end
    end
    return A
end

# ---------------------------------------------------------------------------
# Post-processing for positivity/stochasticity preservation
# ---------------------------------------------------------------------------

function _postprocess!(A::AbstractMatrix; ensure_nonneg::Bool=false, normalize_rows::Bool=false)
    if ensure_nonneg
        row_sums_before = normalize_rows ? vec(sum(A; dims=2)) : nothing
        @. A = max(A, 0.0)
        if normalize_rows && row_sums_before !== nothing
            for i in axes(A, 1)
                s = sum(@view A[i, :])
                if s > 0 && row_sums_before[i] > 0
                    A[i, :] .*= row_sums_before[i] / s
                end
            end
        end
    end
    return A
end

# ---------------------------------------------------------------------------
# Right Kan extension (refinement)
# ---------------------------------------------------------------------------

"""
    right_kan_extension(A::AbstractMatrix, domain::ContinuousProjectionDomain)

Construct a piecewise-constant kernel function from a matrix and domain.

``K_{pw}(z', z) = A_{ij} / h`` where ``z \\in B_j, z' \\in B_i``
"""
function right_kan_extension(A::AbstractMatrix, domain::ContinuousProjectionDomain)
    z_min = domain.lower
    h = step_size(domain)
    n = size(A, 1)
    function piecewise_kernel(z_new, z)
        j = clamp(Int(ceil((z - z_min) / h)), 1, n)
        i = clamp(Int(ceil((z_new - z_min) / h)), 1, n)
        return A[i, j] / h
    end
    return piecewise_kernel
end

function right_kan_extension(A::AbstractMatrix, domain::ContinuousDomain)
    cpd = ContinuousProjectionDomain(domain.lower, domain.upper, domain.n_meshpoints)
    return right_kan_extension(A, cpd)
end
