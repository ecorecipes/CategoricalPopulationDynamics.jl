"""
ProjectionSharer: undirected open systems for projection model composition.

Follows AlgebraicDynamics' ResourceSharer pattern but specialised for
additive kernel/matrix composition in structured population models.
"""

"""
    ProjectionSharer{T<:Real}

An undirected open system wrapping a transition matrix.

Ports represent state variables shared with other sharers.
When composed via `oapply`, sharers at the same junction sum their
matrix contributions (additive operadic algebra).

# Fields
- `nports`: number of exposed ports (state variables)
- `nstates`: internal state dimension (mesh size)
- `matrix`: the `nstates × nstates` transition matrix
- `portmap`: maps port indices to internal state indices
"""
struct ProjectionSharer{T<:Real}
    nports::Int
    nstates::Int
    matrix::Matrix{T}
    portmap::Vector{Int}

    function ProjectionSharer{T}(nports, nstates, matrix, portmap) where {T<:Real}
        size(matrix) == (nstates, nstates) || throw(DimensionMismatch(
            "matrix must be $nstates × $nstates, got $(size(matrix))"))
        length(portmap) == nports || throw(DimensionMismatch(
            "portmap length $(length(portmap)) must equal nports $nports"))
        all(1 .<= portmap .<= nstates) || throw(ArgumentError(
            "portmap entries must be in 1:$nstates"))
        new{T}(nports, nstates, matrix, portmap)
    end
end

"""
    ProjectionSharer(K::AbstractMatrix)

Construct from a matrix with all states as ports (identity portmap).
"""
function ProjectionSharer(K::AbstractMatrix{T}) where {T<:Real}
    n = size(K, 1)
    ProjectionSharer{T}(n, n, Matrix(K), collect(1:n))
end

"""
    ProjectionSharer(kernel_fn, domain::ContinuousProjectionDomain)

Construct from a kernel function and domain via left Kan extension.
"""
function ProjectionSharer(kernel_fn::Function, domain::ContinuousProjectionDomain{T}) where {T}
    A = left_kan_extension(kernel_fn, domain)
    ProjectionSharer(A)
end
