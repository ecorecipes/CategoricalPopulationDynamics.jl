"""
Lean-conformance tests for Rand(C) and Tuljapurkar's inequality.

These tests numerically verify properties proven formally in the
kan_markov_bridge Lean 4 project:

- Dirac roundtrip: E[δ(A)] = A  (RandCategory.lean, Result 106)
- Identity roundtrip: E[δ(I)] = I  (RandCategory.lean, Result 107)
- Tuljapurkar inequality: λ_s ≤ ρ(E[K])  (RandCategory.lean, Result 108)
- Strict inequality when non-degenerate  (EnvStochastic.lean, Result 99 comment)
- Variance decomposition  (EnvStochastic.lean, Result 101)
- Orthogonality: env variance vanishes for constant env  (EnvStochastic.lean, Result 100)
- Model cube: 8 vertices  (RandCategory.lean, Results 109–110)
"""

using Test
using CategoricalPopulationDynamics
using LinearAlgebra
using Random

@testset "Lean Conformance: Rand(C) & Tuljapurkar" begin

    # -----------------------------------------------------------------
    @testset "Dirac roundtrip E[δ(A)] = A (Lean Result 106)" begin
        for n in [2, 3, 5]
            A = rand(MersenneTwister(42), n, n)
            sks = dirac_embed(A)
            E_K = expected_kernel(sks)
            @test E_K ≈ A atol=1e-15
        end
    end

    # -----------------------------------------------------------------
    @testset "Identity roundtrip E[δ(I)] = I (Lean Result 107)" begin
        for n in [2, 4, 6]
            I_n = Matrix{Float64}(I, n, n)
            sks = dirac_embed(I_n)
            E_K = expected_kernel(sks)
            @test E_K ≈ I_n atol=1e-15
        end
    end

    # -----------------------------------------------------------------
    @testset "Dirac preserves growth rate (limit case of Result 108)" begin
        # When distribution is a point mass, λ_s should equal ρ(A)
        A = [0.0 4.0; 0.6 0.0]
        ρ_A = maximum(abs.(eigvals(A)))
        sks = dirac_embed(A)
        result = stochastic_growth_rate(sks;
            horizon=50_000, burn_in=5000, n_replicates=10,
            rng=MersenneTwister(123))
        @test abs(result.lambda_s - ρ_A) < 0.02
    end

    # -----------------------------------------------------------------
    @testset "Tuljapurkar inequality λ_s ≤ ρ(E[K]) (Lean Result 108)" begin
        rng = MersenneTwister(314)

        # Test 1: 2×2 Leslie matrices with environmental variation
        A_good = [0.0 3.5; 0.7 0.0]
        A_bad  = [0.0 1.5; 0.3 0.0]
        sks = StochasticKernelSet([A_good, A_bad], [0.5, 0.5])
        bound = tuljapurkar_bound(sks)
        growth = stochastic_growth_rate(sks;
            horizon=50_000, burn_in=5000, n_replicates=10, rng=rng)
        @test growth.lambda_s ≤ bound.bound + 0.01  # small tolerance for MC error

        # Test 2: 3×3 projection matrices
        M1 = [0.0 0.0 5.0; 0.4 0.0 0.0; 0.0 0.8 0.3]
        M2 = [0.0 0.0 3.0; 0.3 0.0 0.0; 0.0 0.6 0.2]
        M3 = [0.0 0.0 7.0; 0.5 0.0 0.0; 0.0 0.9 0.4]
        sks3 = StochasticKernelSet([M1, M2, M3], [0.4, 0.3, 0.3])
        bound3 = tuljapurkar_bound(sks3)
        growth3 = stochastic_growth_rate(sks3;
            horizon=50_000, burn_in=5000, n_replicates=10, rng=rng)
        @test growth3.lambda_s ≤ bound3.bound + 0.01

        # Test 3: unequal weights
        sks_asym = StochasticKernelSet([A_good, A_bad], [0.9, 0.1])
        bound_asym = tuljapurkar_bound(sks_asym)
        growth_asym = stochastic_growth_rate(sks_asym;
            horizon=50_000, burn_in=5000, n_replicates=10, rng=rng)
        @test growth_asym.lambda_s ≤ bound_asym.bound + 0.01
    end

    # -----------------------------------------------------------------
    @testset "Strict inequality for non-degenerate distributions" begin
        # Tuljapurkar: λ_s < ρ(E[K]) when variance > 0
        A_good = [0.0 5.0; 0.8 0.0]
        A_bad  = [0.0 1.0; 0.2 0.0]
        sks = StochasticKernelSet([A_good, A_bad])
        bound = tuljapurkar_bound(sks)
        growth = stochastic_growth_rate(sks;
            horizon=100_000, burn_in=10000, n_replicates=20,
            rng=MersenneTwister(999))
        # Strict inequality: λ_s should be meaningfully below ρ(E[K])
        @test growth.lambda_s < bound.bound - 0.01
    end

    # -----------------------------------------------------------------
    @testset "Jensen gap increases with environmental variance" begin
        # More variance → larger gap between λ_s and ρ(E[K])
        rng = MersenneTwister(555)

        # Low variance: A ± small perturbation
        A_base = [0.0 3.0; 0.5 0.0]
        A_lo_1 = A_base .+ [0 0.1; 0.01 0]
        A_lo_2 = A_base .- [0 0.1; 0.01 0]
        sks_lo = StochasticKernelSet([A_lo_1, A_lo_2])

        # High variance: A ± large perturbation
        A_hi_1 = A_base .+ [0 2.0; 0.3 0]
        A_hi_2 = A_base .- [0 2.0; 0.3 0]
        # Ensure non-negative
        A_hi_2 = max.(A_hi_2, 0.0)
        sks_hi = StochasticKernelSet([A_hi_1, A_hi_2])

        g_lo = stochastic_growth_rate(sks_lo;
            horizon=80_000, burn_in=5000, n_replicates=15, rng=rng)
        b_lo = tuljapurkar_bound(sks_lo)
        gap_lo = b_lo.bound - g_lo.lambda_s

        g_hi = stochastic_growth_rate(sks_hi;
            horizon=80_000, burn_in=5000, n_replicates=15, rng=rng)
        b_hi = tuljapurkar_bound(sks_hi)
        gap_hi = b_hi.bound - g_hi.lambda_s

        @test gap_hi > gap_lo
    end

    # -----------------------------------------------------------------
    @testset "Constant environment: λ_s ≈ ρ(A) (degenerate Rand)" begin
        # If all environments are identical, λ_s = ρ(A) exactly
        A = [0.0 3.0; 0.5 0.0]
        sks = StochasticKernelSet([A, A, A])  # three copies, same matrix
        bound = tuljapurkar_bound(sks)
        growth = stochastic_growth_rate(sks;
            horizon=50_000, burn_in=5000, n_replicates=10,
            rng=MersenneTwister(777))
        ρ_A = maximum(abs.(eigvals(A)))
        @test abs(growth.lambda_s - ρ_A) < 0.02
        @test abs(bound.bound - ρ_A) < 1e-10
    end

    # -----------------------------------------------------------------
    @testset "Expectation is linear (Lean Result 105)" begin
        A1 = [0.0 2.0; 0.4 0.0]
        A2 = [0.0 4.0; 0.8 0.0]
        w1, w2 = 0.3, 0.7
        sks = StochasticKernelSet([A1, A2], [w1, w2])
        E_K = expected_kernel(sks)
        @test E_K ≈ w1 .* A1 .+ w2 .* A2 atol=1e-14
    end

    # -----------------------------------------------------------------
    @testset "Weight normalization" begin
        A1 = [1.0 0.0; 0.0 2.0]
        A2 = [2.0 0.0; 0.0 1.0]
        # Un-normalized weights
        sks = StochasticKernelSet([A1, A2], [3.0, 7.0])
        @test sks.weights ≈ [0.3, 0.7] atol=1e-14
        E_K = expected_kernel(sks)
        @test E_K ≈ 0.3 .* A1 .+ 0.7 .* A2 atol=1e-14
    end

    # -----------------------------------------------------------------
    @testset "Variance decomposition (Lean Result 101)" begin
        A_good = [0.0 4.0; 0.6 0.0]
        A_bad  = [0.0 2.0; 0.3 0.0]
        sks = StochasticKernelSet([A_good, A_bad], [0.5, 0.5])

        vd = variance_decomposition(sks)

        # Per-environment λ should be spectral radii
        λ1 = maximum(abs.(eigvals(A_good)))
        λ2 = maximum(abs.(eigvals(A_bad)))
        @test vd.lambda_env[1] ≈ λ1 atol=1e-10
        @test vd.lambda_env[2] ≈ λ2 atol=1e-10

        # Weighted mean
        @test vd.mean_lambda ≈ 0.5 * λ1 + 0.5 * λ2 atol=1e-10

        # Variance = Σ w_e (λ_e - mean)²
        expected_var = 0.5 * (λ1 - vd.mean_lambda)^2 + 0.5 * (λ2 - vd.mean_lambda)^2
        @test vd.var_env ≈ expected_var atol=1e-10

        # Variance is positive for non-degenerate
        @test vd.var_env > 0
    end

    # -----------------------------------------------------------------
    @testset "Zero variance for constant environment (Lean Result 100)" begin
        A = [0.0 3.0; 0.5 0.0]
        sks = StochasticKernelSet([A, A])
        vd = variance_decomposition(sks)
        @test vd.var_env ≈ 0.0 atol=1e-14
    end

    # -----------------------------------------------------------------
    @testset "StochasticKernelSet validation" begin
        # Mismatched lengths
        @test_throws ArgumentError StochasticKernelSet(
            [ones(2,2)], [0.5, 0.5])
        # Empty
        @test_throws ArgumentError StochasticKernelSet(
            Matrix{Float64}[], Float64[])
        # Negative weights
        @test_throws ArgumentError StochasticKernelSet(
            [ones(2,2)], [-1.0])
        # Mismatched matrix sizes
        @test_throws ArgumentError StochasticKernelSet(
            [ones(2,2), ones(3,3)], [0.5, 0.5])
    end

    # -----------------------------------------------------------------
    @testset "Model cube vertices (Lean Results 109–110)" begin
        # 8 vertices from 3 binary axes
        vertices = [ModelCubeVertex(d, e, s)
                    for d in [false, true]
                    for e in [false, true]
                    for s in [false, true]]
        @test length(vertices) == 8
        @test length(unique(vertices)) == 8

        # Check string representations
        @test string(ModelCubeVertex(false, false, false)) == "Meas"
        @test string(ModelCubeVertex(false, false, true))  == "Stoch"
        @test string(ModelCubeVertex(true, false, false))  == "Mat"
        @test string(ModelCubeVertex(true, false, true))   == "FinStoch"
        @test string(ModelCubeVertex(false, true, false))  == "Rand(Meas)"
        @test string(ModelCubeVertex(false, true, true))   == "Rand(Stoch)"
        @test string(ModelCubeVertex(true, true, false))   == "Rand(Mat)"
        @test string(ModelCubeVertex(true, true, true))    == "Rand(FinStoch)"
    end

    # -----------------------------------------------------------------
    @testset "Confidence interval contains true value" begin
        # For a Dirac embedding, the true value is known exactly
        A = [0.0 3.0; 0.5 0.0]
        ρ = maximum(abs.(eigvals(A)))
        sks = dirac_embed(A)
        result = stochastic_growth_rate(sks;
            horizon=50_000, burn_in=5000, n_replicates=20,
            rng=MersenneTwister(42))
        # log(ρ) should be within the 95% CI
        @test result.ci_lower ≤ log(ρ) ≤ result.ci_upper
    end

    # -----------------------------------------------------------------
    @testset "Accessor functions" begin
        A1 = ones(3, 3)
        A2 = 2 .* ones(3, 3)
        sks = StochasticKernelSet([A1, A2], [0.6, 0.4])
        @test n_environments(sks) == 2
        @test state_dim(sks) == 3
    end

end
