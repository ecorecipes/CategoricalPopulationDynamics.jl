"""
Stratification: replicate local demography across strata weighted by a coupling matrix.

In the categorical framework, this is a pullback in a slice category.
"""

"""
    stratify(A_local::AbstractMatrix, coupling::AbstractMatrix)

Construct a block-structured matrix from a single local transition matrix
and a coupling (dispersal) matrix.  Every stratum shares the same local dynamics.

``A_{strat}[(s_{to}, i), (s_{from}, j)] = D[s_{to}, s_{from}] \\cdot A_{local}[i, j]``
"""
function stratify(A_local::AbstractMatrix, coupling::AbstractMatrix)
    size(A_local, 1) == size(A_local, 2) ||
        throw(DimensionMismatch("local matrix must be square, got $(size(A_local))"))
    size(coupling, 1) == size(coupling, 2) ||
        throw(DimensionMismatch("coupling matrix must be square, got $(size(coupling))"))
    n_bins = size(A_local, 1)
    n_strata = size(coupling, 1)
    n_total = n_bins * n_strata
    T = promote_type(eltype(A_local), eltype(coupling))
    A_strat = zeros(T, n_total, n_total)
    for s_to in 1:n_strata
        for s_from in 1:n_strata
            rows = ((s_to - 1) * n_bins + 1):(s_to * n_bins)
            cols = ((s_from - 1) * n_bins + 1):(s_from * n_bins)
            A_strat[rows, cols] .= coupling[s_to, s_from] .* A_local
        end
    end
    return A_strat
end

"""
    stratify(A_locals::AbstractVector{<:AbstractMatrix}, coupling::AbstractMatrix)

Heterogeneous stratification: each stratum has its own local transition matrix,
connected by a coupling matrix.  This is the natural generalisation for cases
where strata differ in their internal dynamics (e.g. genotype-specific vital
rates, latitude-dependent development).

``A_{strat}[(s_{to}, i), (s_{from}, j)] = D[s_{to}, s_{from}] \\cdot A_{s_{from}}[i, j]``

The key difference from the homogeneous method is that the *source* stratum's
matrix ``A_{s_{from}}`` is used, so individuals develop under their own
stratum's rates before being redistributed by the coupling matrix.

Combine with `compose_transitions` for process-specific coupling, e.g.
block-diagonal survival (identity coupling) plus cross-stratum fecundity
(mating/dispersal coupling):

```julia
A = compose_transitions(Dict(
    :survival  => stratify([P₁, P₂, P₃], I(3)),
    :fecundity => stratify([F₁, F₂, F₃], M_mating)))
```
"""
function stratify(A_locals::AbstractVector{<:AbstractMatrix}, coupling::AbstractMatrix)
    n_strata = length(A_locals)
    size(coupling) == (n_strata, n_strata) ||
        throw(DimensionMismatch("coupling matrix must be $(n_strata)×$(n_strata), got $(size(coupling))"))
    n_bins = size(first(A_locals), 1)
    all(size(A) == (n_bins, n_bins) for A in A_locals) ||
        throw(DimensionMismatch("all local matrices must be $(n_bins)×$(n_bins)"))
    T = promote_type(eltype.(A_locals)..., eltype(coupling))
    n_total = n_bins * n_strata
    A_strat = zeros(T, n_total, n_total)
    for s_to in 1:n_strata
        for s_from in 1:n_strata
            rows = ((s_to - 1) * n_bins + 1):(s_to * n_bins)
            cols = ((s_from - 1) * n_bins + 1):(s_from * n_bins)
            A_strat[rows, cols] .= coupling[s_to, s_from] .* A_locals[s_from]
        end
    end
    return A_strat
end
