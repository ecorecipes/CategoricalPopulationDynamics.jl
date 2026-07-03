"""
Adjunction diagnostics for the Lan_D ⊣ D* ⊣ Ran_D chain.

Measures how well discretisation and refinement preserve model properties.
Includes theoretical error bounds from the Lean formalization.
"""

"""
    unit_error(A::AbstractMatrix, domain::ContinuousProjectionDomain; rule=:midpoint)

Round-trip error for the unit of the adjunction: A → Ran_D(A) → Lan_D(Ran_D(A)).

Returns relative Frobenius norm error ‖A' - A‖ / ‖A‖.
For a self-consistent discretisation this should be ≈ 0.
"""
function unit_error(A::AbstractMatrix, domain::ContinuousProjectionDomain;
                    rule::Symbol=:midpoint)
    K_pw = right_kan_extension(A, domain)
    A_prime = left_kan_extension(K_pw, domain; rule=rule)
    nA = norm(A)
    nA == 0 && return 0.0
    return norm(A_prime - A) / nA
end

"""
    counit_error(kernel_fn, domain::ContinuousProjectionDomain; rule=:midpoint, n_quad=1000)

Round-trip error for the counit: K → Lan_D(K) → Ran_D(Lan_D(K)).

Approximates the L2 error between the original kernel and the
piecewise-constant reconstruction via numerical quadrature.
"""
function counit_error(kernel_fn, domain::ContinuousProjectionDomain;
                      rule::Symbol=:midpoint, n_quad::Int=1000)
    A = left_kan_extension(kernel_fn, domain; rule=rule)
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
    adjunction_errors(kernel_fn, domain::ContinuousProjectionDomain; rule=:midpoint, n_quad=1000)

Compute both unit and counit errors, plus a growth-rate comparison between the
requested discretisation and an independent higher-resolution reference
discretisation of the kernel.

Returns a NamedTuple `(unit, counit, lambda_kernel, lambda_matrix, rule)`.
"""
function adjunction_errors(kernel_fn, domain::ContinuousProjectionDomain;
                           rule::Symbol=:midpoint, n_quad::Int=1000,
                           reference_rule::Symbol=:simpson,
                           reference_n::Union{Nothing, Int}=nothing)
    A = left_kan_extension(kernel_fn, domain; rule=rule)
    K_pw = right_kan_extension(A, domain)
    A_roundtrip = left_kan_extension(K_pw, domain; rule=rule)

    nA = norm(A)
    ue = nA == 0 ? 0.0 : norm(A_roundtrip - A) / nA
    ce = counit_error(kernel_fn, domain; rule=rule, n_quad=n_quad)
    λ_matrix = lambda(A)
    ref_n = isnothing(reference_n) ? max(4 * domain.n_meshpoints, 200) : reference_n
    ref_domain = ContinuousProjectionDomain(domain.lower, domain.upper, ref_n)
    λ_kernel = lambda(left_kan_extension(kernel_fn, ref_domain; rule=reference_rule))

    return (unit=ue, counit=ce, lambda_kernel=λ_kernel, lambda_matrix=λ_matrix, rule=rule)
end

"""
    convergence_analysis(kernel_fn, mesh_sizes; rule=:midpoint, reference_rule=:simpson, reference_n=500)

Empirical convergence analysis: compute λ at each mesh size and estimate
the convergence rate by log-log regression.

Returns a NamedTuple with fields:
- `mesh_sizes`: the input sizes
- `lambdas`: λ at each mesh size
- `errors`: |λ_n - λ_ref| at each size
- `estimated_order`: slope of log(error) vs log(h)
- `reference_lambda`: λ computed at high resolution
"""
function convergence_analysis(kernel_fn, domain_template::ContinuousProjectionDomain,
                              mesh_sizes::AbstractVector{Int};
                              rule::Symbol=:midpoint,
                              reference_rule::Symbol=:simpson,
                              reference_n::Int=500)
    lo, hi = domain_template.lower, domain_template.upper

    # Reference solution at high resolution
    ref_domain = ContinuousProjectionDomain(lo, hi, reference_n)
    A_ref = left_kan_extension(kernel_fn, ref_domain; rule=reference_rule)
    λ_ref = lambda(A_ref)

    lambdas = Float64[]
    errors = Float64[]
    hs = Float64[]
    for n in mesh_sizes
        d = ContinuousProjectionDomain(lo, hi, n)
        A = left_kan_extension(kernel_fn, d; rule=rule)
        λ = lambda(A)
        push!(lambdas, λ)
        push!(errors, abs(λ - λ_ref))
        push!(hs, step_size(d))
    end

    # Log-log regression for convergence order (skip zero errors)
    valid = errors .> 0
    if count(valid) >= 2
        log_h = log.(hs[valid])
        log_e = log.(errors[valid])
        n_v = length(log_h)
        slope = (n_v * sum(log_h .* log_e) - sum(log_h) * sum(log_e)) /
                (n_v * sum(log_h .^ 2) - sum(log_h)^2)
    else
        slope = NaN
    end

    return (mesh_sizes=mesh_sizes, lambdas=lambdas, errors=errors,
            step_sizes=hs, estimated_order=slope, reference_lambda=λ_ref)
end
