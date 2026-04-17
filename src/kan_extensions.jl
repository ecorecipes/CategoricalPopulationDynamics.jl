"""
Kan extension functors between kernel spaces and matrix spaces.

- **Left Kan extension** (Lan_D): kernel → matrix (discretisation)
- **Right Kan extension** (Ran_D): matrix → piecewise-constant kernel (refinement)

These form the adjunction chain: Lan_D ⊣ D* ⊣ Ran_D
"""

"""
    left_kan_extension(kernel_fn, domain::ContinuousProjectionDomain)

Discretise a continuous kernel `kernel_fn(z_new, z)` into a matrix using the
midpoint rule.

``A_{ij} = h \\cdot K(z_i, z_j)``
"""
function left_kan_extension(kernel_fn, domain::ContinuousProjectionDomain)
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

function left_kan_extension(kernel_fn, domain::ContinuousDomain)
    cpd = ContinuousProjectionDomain(domain.lower, domain.upper, domain.n_meshpoints)
    return left_kan_extension(kernel_fn, cpd)
end

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
