"""
Adjunction diagnostics for the Lan_D ⊣ D* ⊣ Ran_D chain.

Measures how well discretisation and refinement preserve model properties.
"""

"""
    unit_error(A::AbstractMatrix, domain::ContinuousProjectionDomain)

Round-trip error for the unit of the adjunction: A → Ran_D(A) → Lan_D(Ran_D(A)).

Returns relative Frobenius norm error ‖A' - A‖ / ‖A‖.
For a self-consistent discretisation this should be ≈ 0.
"""
function unit_error(A::AbstractMatrix, domain::ContinuousProjectionDomain)
    K_pw = right_kan_extension(A, domain)
    A_prime = left_kan_extension(K_pw, domain)
    nA = norm(A)
    nA == 0 && return 0.0
    return norm(A_prime - A) / nA
end

"""
    counit_error(kernel_fn, domain::ContinuousProjectionDomain; n_quad=1000)

Round-trip error for the counit: K → Lan_D(K) → Ran_D(Lan_D(K)).

Approximates the L2 error between the original kernel and the
piecewise-constant reconstruction via numerical quadrature.
"""
function counit_error(kernel_fn, domain::ContinuousProjectionDomain; n_quad::Int=1000)
    A = left_kan_extension(kernel_fn, domain)
    K_pw = right_kan_extension(A, domain)

    z_quad = range(domain.lower, domain.upper; length=n_quad)
    err_sq = 0.0
    orig_sq = 0.0
    dz = (domain.upper - domain.lower) / (n_quad - 1)
    for z in z_quad
        for z_new in z_quad
            k_orig = kernel_fn(z_new, z)
            k_recon = K_pw(z_new, z)
            err_sq += (k_orig - k_recon)^2 * dz^2
            orig_sq += k_orig^2 * dz^2
        end
    end
    orig_sq == 0 && return 0.0
    return sqrt(err_sq / orig_sq)
end

"""
    adjunction_errors(kernel_fn, domain::ContinuousProjectionDomain; n_quad=1000)

Compute both unit and counit errors, plus lambda comparison.

Returns a NamedTuple `(unit, counit, lambda_kernel, lambda_matrix)`.
"""
function adjunction_errors(kernel_fn, domain::ContinuousProjectionDomain; n_quad::Int=1000)
    A = left_kan_extension(kernel_fn, domain)
    K_pw = right_kan_extension(A, domain)
    A_roundtrip = left_kan_extension(K_pw, domain)

    nA = norm(A)
    ue = nA == 0 ? 0.0 : norm(A_roundtrip - A) / nA
    ce = counit_error(kernel_fn, domain; n_quad=n_quad)
    λ_matrix = lambda(A)
    λ_kernel = lambda(left_kan_extension(kernel_fn, domain))

    return (unit=ue, counit=ce, lambda_kernel=λ_kernel, lambda_matrix=λ_matrix)
end
