"""
Coarsening: pushforward of transition matrices along bin-aggregation maps.

Uses Catlab `FinFunction` for the general case and domain pairs for convenience.
"""

"""
    coarsen(A::AbstractMatrix, f::FinFunction)

Coarsen a transition matrix via pushforward along a Catlab `FinFunction`.

The FinFunction `f: FinSet(n_fine) → FinSet(n_coarse)` maps fine bin
indices to coarse bin indices.
"""
function _check_square_matrix(A::AbstractMatrix)
    size(A, 1) == size(A, 2) || throw(DimensionMismatch(
        "coarsen expects a square matrix, got size $(size(A))"))
end

function coarsen(A::AbstractMatrix, f::FinFunction)
    _check_square_matrix(A)
    n_fine = length(dom(f))
    n_coarse = length(codom(f))
    n_fine == size(A, 1) || throw(DimensionMismatch(
        "Matrix size $(size(A, 1)) does not match FinFunction domain $n_fine"))

    fibre_sizes = zeros(Int, n_coarse)
    for i in 1:n_fine
        fibre_sizes[f(i)] += 1
    end

    A_coarse = zeros(eltype(A), n_coarse, n_coarse)
    for j_fine in 1:n_fine
        c_j = f(j_fine)
        for i_fine in 1:n_fine
            c_i = f(i_fine)
            A_coarse[c_i, c_j] += A[i_fine, j_fine] / fibre_sizes[c_j]
        end
    end
    return A_coarse
end

"""
    coarsen(A::AbstractMatrix, from::ContinuousProjectionDomain, to::ContinuousProjectionDomain)

Coarsen a transition matrix from a fine domain to a coarser domain.
Constructs the FinFunction internally from the domain pair.
"""
function coarsen(A::AbstractMatrix,
        from::ContinuousProjectionDomain,
        to::ContinuousProjectionDomain)
    _check_square_matrix(A)
    n_fine = from.n_meshpoints
    n_coarse = to.n_meshpoints
    n_fine == size(A, 1) || throw(DimensionMismatch(
        "Matrix size $(size(A, 1)) does not match from_domain meshpoints $n_fine"))
    n_fine % n_coarse == 0 || throw(ArgumentError(
        "n_fine ($n_fine) must be a multiple of n_coarse ($n_coarse)"))
    bins_per_coarse = n_fine ÷ n_coarse

    f = FinFunction(
        [((i - 1) ÷ bins_per_coarse) + 1 for i in 1:n_fine],
        n_coarse)
    return coarsen(A, f)
end

function coarsen(A::AbstractMatrix,
        from::ContinuousDomain,
        to::ContinuousDomain)
    cpd_from = ContinuousProjectionDomain(from.lower, from.upper, from.n_meshpoints)
    cpd_to = ContinuousProjectionDomain(to.lower, to.upper, to.n_meshpoints)
    return coarsen(A, cpd_from, cpd_to)
end
