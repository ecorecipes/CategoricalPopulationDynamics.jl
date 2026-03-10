"""
Stratification: replicate local demography across patches weighted by dispersal.

In the categorical framework, this is a pullback in a slice category.
"""

"""
    stratify(A_local::AbstractMatrix, dispersal::AbstractMatrix)

Construct a block-structured spatial matrix from a local transition matrix
and a dispersal matrix.

``A_{strat}[(p_{to}, i), (p_{from}, j)] = D[p_{to}, p_{from}] \\cdot A_{local}[i, j]``
"""
function stratify(A_local::AbstractMatrix, dispersal::AbstractMatrix)
    n_bins = size(A_local, 1)
    n_patches = size(dispersal, 1)
    n_total = n_bins * n_patches
    A_strat = zeros(eltype(A_local), n_total, n_total)
    for p_to in 1:n_patches
        for p_from in 1:n_patches
            rows = ((p_to - 1) * n_bins + 1):(p_to * n_bins)
            cols = ((p_from - 1) * n_bins + 1):(p_from * n_bins)
            A_strat[rows, cols] .= dispersal[p_to, p_from] .* A_local
        end
    end
    return A_strat
end
