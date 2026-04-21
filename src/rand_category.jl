"""
Environmental stochasticity via the Rand(C) construction.

Formalizes the Lean `RandCategory.lean` and `EnvStochastic.lean` results:
- `StochasticKernelSet`: weighted iid kernel collection (Lean: `StochEnv`)
- `stochastic_growth_rate`: Lyapunov exponent λ_s = exp(E[log λ(K_{eₜ})])
  (Lean: Result 98)
- `tuljapurkar_bound`: upper bound ρ(E[K]) ≥ λ_s (Lean: Result 99)
- `variance_decomposition`: environmental + demographic (Lean: Result 101)

## Model cube classification (Lean: Results 109–110)

The 8 model types arise from 3 binary axes:
- Discretisation: continuous (Meas/Stoch) vs discrete (Mat/FinStoch)
- Environmental: deterministic vs random (Rand(·))
- Demographic: deterministic vs stochastic
"""

using LinearAlgebra
using Random

# ---------------------------------------------------------------------------
# StochasticKernelSet: Rand(C) morphism
# ---------------------------------------------------------------------------

"""
    StochasticKernelSet{T<:AbstractMatrix}

A collection of transition matrices with associated probabilities,
representing an iid environmental stochasticity model.

Corresponds to Lean's `RandMorph` (RandCategory.lean, Result 103):
- `morphisms`: `Fin n_env → Mat(n, n)`
- `weights`: `Fin n_env → ℝ` with `sum(weights) = 1`

## Assumptions
- Environments are drawn **iid** from the weight distribution
- Each kernel `matrices[e]` should be a valid (non-negative) transition matrix
- For Tuljapurkar's inequality: kernels should be primitive (irreducible + aperiodic)
"""
struct StochasticKernelSet{T<:AbstractMatrix}
    matrices::Vector{T}
    weights::Vector{Float64}

    function StochasticKernelSet(matrices::Vector{T}, weights::Vector{Float64}) where {T<:AbstractMatrix}
        length(matrices) == length(weights) ||
            throw(ArgumentError("matrices and weights must have the same length"))
        length(matrices) > 0 ||
            throw(ArgumentError("must provide at least one matrix"))
        all(w -> w >= 0, weights) ||
            throw(ArgumentError("weights must be non-negative"))
        s = sum(weights)
        s > 0 || throw(ArgumentError("weights must sum to a positive value"))
        # Normalize
        w_normalized = weights ./ s
        n = size(matrices[1], 1)
        all(M -> size(M) == (n, n), matrices) ||
            throw(ArgumentError("all matrices must be the same size"))
        new{T}(matrices, w_normalized)
    end
end

"""Construct with uniform weights."""
StochasticKernelSet(matrices::Vector{T}) where {T<:AbstractMatrix} =
    StochasticKernelSet(matrices, ones(length(matrices)))

"""Number of environmental states."""
n_environments(sks::StochasticKernelSet) = length(sks.matrices)

"""State dimension (n × n matrices)."""
state_dim(sks::StochasticKernelSet) = size(sks.matrices[1], 1)

# ---------------------------------------------------------------------------
# Dirac embedding: δ(A) — deterministic matrix as trivial random environment
# Lean: Result 104 (diracEmbed)
# ---------------------------------------------------------------------------

"""
    dirac_embed(A::AbstractMatrix)

Embed a deterministic matrix as a `StochasticKernelSet` with a single
environment of weight 1. (Lean: `diracEmbed`, Result 104)
"""
dirac_embed(A::AbstractMatrix) = StochasticKernelSet([A], [1.0])

# ---------------------------------------------------------------------------
# Expectation functor: E[K] = Σ_e w_e K_e
# Lean: Result 105 (randExpect)
# ---------------------------------------------------------------------------

"""
    expected_kernel(sks::StochasticKernelSet)

Compute the mean kernel E[K] = Σ_e w_e · K_e.
(Lean: `envMeanKernel`, `randExpect`, Results 97/105)

Left inverse of `dirac_embed`: `expected_kernel(dirac_embed(A)) == A`.
(Lean: Result 106)
"""
function expected_kernel(sks::StochasticKernelSet)
    E_K = zeros(state_dim(sks), state_dim(sks))
    for (M, w) in zip(sks.matrices, sks.weights)
        E_K .+= w .* M
    end
    return E_K
end

# ---------------------------------------------------------------------------
# Stochastic growth rate: Lyapunov exponent
# Lean: Result 98 (λ_s = exp(E[log λ(K_{eₜ})]))
# ---------------------------------------------------------------------------

"""
    stochastic_growth_rate(sks::StochasticKernelSet;
                           horizon=10_000, burn_in=1000, n_replicates=5,
                           rng=Random.default_rng())

Estimate the stochastic growth rate λ_s via simulation of a random matrix
product.

The stochastic growth rate is the Lyapunov exponent:
    log(λ_s) = lim_{T→∞} (1/T) · log ‖A_{eₜ} ⋯ A_{e₁} n₀‖

where environments `eₜ` are drawn iid from the weight distribution.

Returns a NamedTuple with:
- `lambda_s`: estimated stochastic growth rate
- `log_lambda_s`: log of stochastic growth rate (Lyapunov exponent)
- `se`: standard error across replicates
- `ci_lower`, `ci_upper`: 95% confidence interval for log(λ_s)
- `horizon`, `burn_in`, `n_replicates`: simulation parameters used

## References
- Tuljapurkar (1990), "Population Dynamics in Variable Environments"
- Lean: `EnvStochastic.lean`, Result 98
"""
function stochastic_growth_rate(sks::StochasticKernelSet;
                                horizon::Int=10_000,
                                burn_in::Int=1000,
                                n_replicates::Int=5,
                                rng::AbstractRNG=Random.default_rng())
    n = state_dim(sks)
    cum_weights = cumsum(sks.weights)

    log_lambdas = Float64[]
    for _ in 1:n_replicates
        # Random initial vector (positive)
        v = rand(rng, n)
        v ./= sum(v)

        log_growth_sum = 0.0
        count = 0
        for t in 1:(horizon + burn_in)
            # Sample environment
            u = rand(rng)
            e = searchsortedfirst(cum_weights, u)
            e = clamp(e, 1, length(sks.matrices))

            # Apply matrix
            v_new = sks.matrices[e] * v
            growth = sum(v_new)
            if growth > 0
                v_new ./= growth
                if t > burn_in
                    log_growth_sum += log(growth)
                    count += 1
                end
            end
            v = v_new
        end
        push!(log_lambdas, log_growth_sum / count)
    end

    mean_log_λ = sum(log_lambdas) / length(log_lambdas)
    se = if length(log_lambdas) > 1
        std_dev = sqrt(sum((x - mean_log_λ)^2 for x in log_lambdas) / (length(log_lambdas) - 1))
        std_dev / sqrt(length(log_lambdas))
    else
        NaN
    end

    return (
        lambda_s = exp(mean_log_λ),
        log_lambda_s = mean_log_λ,
        se = se,
        ci_lower = mean_log_λ - 1.96 * se,
        ci_upper = mean_log_λ + 1.96 * se,
        horizon = horizon,
        burn_in = burn_in,
        n_replicates = n_replicates
    )
end

# ---------------------------------------------------------------------------
# Tuljapurkar's bound: λ_s ≤ ρ(E[K])
# Lean: Result 99/108
# ---------------------------------------------------------------------------

"""
    tuljapurkar_bound(sks::StochasticKernelSet)

Compute the Tuljapurkar upper bound on the stochastic growth rate:
    λ_s ≤ ρ(E[K])

where ρ denotes the spectral radius (dominant eigenvalue).

This follows from Jensen's inequality applied to the concave function
`log ρ(·)` and Kingman's subadditive ergodic theorem.

Returns a NamedTuple with:
- `bound`: ρ(E[K]) — upper bound on λ_s
- `is_primitive`: whether E[K] is primitive (required for strict inequality)
- `expected_kernel`: the mean kernel E[K]

## Assumptions (for the bound to be valid)
- Environments are iid
- All kernels are non-negative
- E[K] is primitive (irreducible and aperiodic)

(Lean: `tuljapurkar_spectral_contraction`, Results 99/108)
"""
function tuljapurkar_bound(sks::StochasticKernelSet)
    E_K = expected_kernel(sks)
    evals = eigvals(E_K)
    ρ = maximum(abs.(evals))

    # Check primitivity: irreducible + aperiodic
    n = state_dim(sks)
    is_prim = _is_primitive(E_K)

    return (bound=ρ, is_primitive=is_prim, expected_kernel=E_K)
end

"""Check if a non-negative matrix is primitive (some power has all positive entries)."""
function _is_primitive(A::AbstractMatrix; max_power::Int=0)
    n = size(A, 1)
    if max_power == 0
        max_power = n^2  # sufficient for primitive matrices
    end
    B = copy(A)
    for _ in 1:max_power
        B = B * A
        if all(x -> x > 0, B)
            return true
        end
    end
    return false
end

# ---------------------------------------------------------------------------
# Variance decomposition
# Lean: Result 101
# ---------------------------------------------------------------------------

"""
    variance_decomposition(sks::StochasticKernelSet)

Decompose growth-rate variance into environmental and sampling components:
    Var[λ] ≈ Var_env[λ_e] + Var_demo/N

Returns a NamedTuple with:
- `lambda_env`: vector of per-environment dominant eigenvalues
- `mean_lambda`: weighted mean of per-environment λ
- `var_env`: weighted variance of per-environment λ (environmental component)

(Lean: `variance_decomposition`, Result 101)
"""
function variance_decomposition(sks::StochasticKernelSet)
    lambdas = [maximum(abs.(eigvals(M))) for M in sks.matrices]
    mean_λ = sum(sks.weights .* lambdas)
    var_env = sum(sks.weights .* (lambdas .- mean_λ).^2)

    return (lambda_env=lambdas, mean_lambda=mean_λ, var_env=var_env)
end

# ---------------------------------------------------------------------------
# Model cube classification
# Lean: Results 109-110
# ---------------------------------------------------------------------------

"""
    ModelCubeVertex

Classification of a structured population model along three binary axes:
- `discrete`: true if state is discretised (Mat/FinStoch), false if continuous (Meas/Stoch)
- `env_stochastic`: true if environmental stochasticity (Rand(·))
- `demo_stochastic`: true if demographic stochasticity (finite-N sampling)

The 8 vertices correspond to categories in the commutative cube:
  Meas → Stoch → Mat → FinStoch (+ Rand(·) versions of each)
"""
struct ModelCubeVertex
    discrete::Bool
    env_stochastic::Bool
    demo_stochastic::Bool
end

function Base.show(io::IO, v::ModelCubeVertex)
    state = v.discrete ? "Mat" : "Meas"
    demo = v.demo_stochastic ? "Stoch" : ""
    if v.demo_stochastic
        state = v.discrete ? "FinStoch" : "Stoch"
    end
    env = v.env_stochastic ? "Rand($state)" : state
    print(io, env)
end
