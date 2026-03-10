using Test
using CategoricalProjectionModels
using Catlab
using Catlab.CategoricalAlgebra
using Catlab.WiringDiagrams
using Catlab.Programs: @relation
using LinearAlgebra
using MatrixProjectionModels
using ProjectionModels: lambda

# ---------------------------------------------------------------------------
# Test data: simple IPM kernel (survival/growth + fecundity)
# ---------------------------------------------------------------------------

# Logistic survival
s(z) = 1.0 / (1.0 + exp(-(0.5 + 0.3 * z)))

# Normal growth kernel
g(z_new, z; μ_slope=0.8, μ_int=0.2, σ=0.5) =
    exp(-0.5 * ((z_new - (μ_int + μ_slope * z)) / σ)^2) / (σ * sqrt(2π))

# Fecundity
f_rate(z) = exp(0.1 + 0.2 * z)
recruit_dist(z_new; μ=0.5, σ=0.3) =
    exp(-0.5 * ((z_new - μ) / σ)^2) / (σ * sqrt(2π))

# Sub-kernels
P_kernel(z_new, z) = s(z) * g(z_new, z)
F_kernel(z_new, z) = f_rate(z) * recruit_dist(z_new)

domain = ContinuousProjectionDomain(0.0, 5.0, 50)

# ---------------------------------------------------------------------------
@testset "CategoricalProjectionModels.jl" begin
# ---------------------------------------------------------------------------

@testset "Schemas" begin
    @testset "ProjectionNet construction" begin
        pn = ProjectionNet()
        add_parts!(pn, :S, 2)
        add_parts!(pn, :T, 1)
        add_part!(pn, :Src; src_t=1, src_s=1)
        add_part!(pn, :Tgt; tgt_t=1, tgt_s=2)
        @test n_states(pn) == 2
        @test n_transitions(pn) == 1
        @test sources(pn, 1) == [1]
        @test targets(pn, 1) == [2]
    end

    @testset "LabelledProjectionNet convenience constructor" begin
        net = LabelledProjectionNet([:size],
            :survival_growth => (:size => :size),
            :fecundity => (:size => :size))
        @test n_states(net) == 1
        @test n_transitions(net) == 2
        @test sname(net) == [:size]
        @test Set(tname(net)) == Set([:survival_growth, :fecundity])
        @test sname(net, 1) == :size
    end

    @testset "Multi-state net" begin
        net = LabelledProjectionNet([:juvenile, :adult],
            :growth => (:juvenile => :adult),
            :survival => (:adult => :adult),
            :reproduction => (:adult => :juvenile))
        @test n_states(net) == 2
        @test n_transitions(net) == 3
    end

    @testset "Open projection nets" begin
        pn = ProjectionNet()
        add_parts!(pn, :S, 2)
        add_part!(pn, :T)
        add_part!(pn, :Src; src_t=1, src_s=1)
        add_part!(pn, :Tgt; tgt_t=1, tgt_s=2)
        opn = Open(pn, [1], [2])
        @test opn isa OpenProjectionNet
    end
end

@testset "Domain types" begin
    @testset "ContinuousProjectionDomain" begin
        d = ContinuousProjectionDomain(0.0, 10.0, 100)
        @test n_meshpoints(d) == 100
        z = meshpoints(d)
        @test length(z) == 100
        @test z[1] ≈ 0.05
        @test z[end] ≈ 9.95
        @test step_size(d) ≈ 0.1
        b = bounds(d)
        @test length(b) == 101
        @test b[1] ≈ 0.0
        @test b[end] ≈ 10.0
    end

    @testset "ContinuousProjectionDomain promotion" begin
        d = ContinuousProjectionDomain(0, 10.0, 50)
        @test d.lower isa Float64
    end

    @testset "ContinuousProjectionDomain validation" begin
        @test_throws ArgumentError ContinuousProjectionDomain(10.0, 0.0, 50)
        @test_throws ArgumentError ContinuousProjectionDomain(0.0, 10.0, 0)
    end

    @testset "DiscreteProjectionDomain" begin
        d = DiscreteProjectionDomain(3)
        @test n_meshpoints(d) == 3
        d2 = DiscreteProjectionDomain([:small, :medium, :large])
        @test n_meshpoints(d2) == 3
        @test d2.labels == [:small, :medium, :large]
    end

    @testset "TransitionSpec" begin
        ts = TransitionSpec(:survival, P_kernel)
        @test ts.name == :survival
        @test ts.data === P_kernel
    end
end

@testset "Kan extensions" begin
    @testset "Left Kan extension" begin
        A = left_kan_extension(P_kernel, domain)
        @test size(A) == (50, 50)
        @test all(A .>= 0)
        # Column sums should be ≤ 1 (survival kernel)
        @test all(sum(A; dims=1) .<= 1.0 + 1e-10)
    end

    @testset "Right Kan extension" begin
        A = left_kan_extension(P_kernel, domain)
        K_pw = right_kan_extension(A, domain)
        @test K_pw isa Function
        z = meshpoints(domain)
        # Piecewise kernel at midpoints should reconstruct matrix entries
        h = step_size(domain)
        @test K_pw(z[1], z[1]) ≈ A[1, 1] / h
    end

    @testset "Round-trip (unit): A → Ran → Lan → A'" begin
        A = left_kan_extension(P_kernel, domain)
        K_pw = right_kan_extension(A, domain)
        A_prime = left_kan_extension(K_pw, domain)
        @test A_prime ≈ A atol=1e-10
    end
end

@testset "Stratification" begin
    A_local = left_kan_extension(P_kernel, domain)
    D = [0.8 0.2; 0.3 0.7]  # 2-patch dispersal
    A_strat = stratify(A_local, D)
    @test size(A_strat) == (100, 100)

    # Check block structure: top-left = 0.8 * A_local
    n = 50
    @test A_strat[1:n, 1:n] ≈ 0.8 * A_local
    @test A_strat[1:n, (n+1):2n] ≈ 0.2 * A_local
    @test A_strat[(n+1):2n, 1:n] ≈ 0.3 * A_local
    @test A_strat[(n+1):2n, (n+1):2n] ≈ 0.7 * A_local
end

@testset "Coarsening" begin
    fine_domain = ContinuousProjectionDomain(0.0, 5.0, 100)
    coarse_domain = ContinuousProjectionDomain(0.0, 5.0, 50)

    A_fine = left_kan_extension(P_kernel, fine_domain)

    @testset "Domain-pair coarsening" begin
        A_coarse = coarsen(A_fine, fine_domain, coarse_domain)
        @test size(A_coarse) == (50, 50)
        # Lambda should be approximately preserved
        λ_fine = lambda(A_fine)
        λ_coarse = lambda(A_coarse)
        @test isapprox(λ_fine, λ_coarse; rtol=0.05)
    end

    @testset "FinFunction coarsening" begin
        f = FinFunction([((i-1) ÷ 2) + 1 for i in 1:100], 50)
        A_coarse_ff = coarsen(A_fine, f)
        @test size(A_coarse_ff) == (50, 50)
    end

    @testset "FinFunction == domain-pair consistency" begin
        A_coarse_dp = coarsen(A_fine, fine_domain, coarse_domain)
        f = FinFunction([((i-1) ÷ 2) + 1 for i in 1:100], 50)
        A_coarse_ff = coarsen(A_fine, f)
        @test A_coarse_dp ≈ A_coarse_ff
    end

    @testset "Coarsening validation" begin
        bad_domain = ContinuousProjectionDomain(0.0, 5.0, 30)
        @test_throws ArgumentError coarsen(A_fine, fine_domain, bad_domain)
    end
end

@testset "Diagnostics" begin
    @testset "Unit error ≈ 0" begin
        A = left_kan_extension(P_kernel, domain)
        ue = unit_error(A, domain)
        @test ue < 1e-10
    end

    @testset "Counit error > 0 for smooth kernel" begin
        ce = counit_error(P_kernel, domain; n_quad=200)
        @test ce > 0
        @test ce < 1.0  # should be reasonable
    end

    @testset "adjunction_errors" begin
        errs = adjunction_errors(P_kernel, domain; n_quad=200)
        @test errs.unit < 1e-10
        @test errs.counit > 0
        @test errs.lambda_kernel ≈ errs.lambda_matrix
        @test errs.lambda_matrix > 0
    end
end

@testset "ProjectionSharer" begin
    @testset "From matrix" begin
        A = left_kan_extension(P_kernel, domain)
        ps = ProjectionSharer(A)
        @test ps.nstates == 50
        @test ps.nports == 50
        @test ps.matrix ≈ A
        @test ps.portmap == Base.collect(1:50)
    end

    @testset "From kernel + domain" begin
        ps = ProjectionSharer(P_kernel, domain)
        @test ps.nstates == 50
        A_direct = left_kan_extension(P_kernel, domain)
        @test ps.matrix ≈ A_direct
    end

    @testset "Validation" begin
        # Matrix size doesn't match nstates
        @test_throws DimensionMismatch ProjectionSharer{Float64}(
            2, 3, zeros(2, 2), [1, 2])
        # portmap entries out of range
        @test_throws ArgumentError ProjectionSharer{Float64}(
            2, 2, zeros(2, 2), [1, 3])
    end
end

@testset "Composition" begin
    A_P = left_kan_extension(P_kernel, domain)
    A_F = left_kan_extension(F_kernel, domain)

    @testset "compose_transitions" begin
        K = compose_transitions(Dict(:P => A_P, :F => A_F))
        @test K ≈ A_P + A_F
    end

    @testset "oapply with UWD" begin
        uwd = @relation (z, z_new) begin
            survive_grow(z, z_new)
            reproduce(z, z_new)
        end

        ps_P = ProjectionSharer(A_P)
        ps_F = ProjectionSharer(A_F)
        result = oapply(uwd, [ps_P, ps_F])
        @test result.matrix ≈ A_P + A_F
    end

    @testset "oapply with Dict" begin
        uwd = @relation (z, z_new) begin
            survive_grow(z, z_new)
            reproduce(z, z_new)
        end

        sharers = Dict(
            :survive_grow => ProjectionSharer(A_P),
            :reproduce => ProjectionSharer(A_F))
        result = oapply(uwd, sharers)
        @test result.matrix ≈ A_P + A_F
    end

    @testset "compose_from_uwd" begin
        uwd = @relation (z, z_new) begin
            survive_grow(z, z_new)
            reproduce(z, z_new)
        end

        sub_kernels = Dict(
            :survive_grow => P_kernel,
            :reproduce => F_kernel)

        K = compose_from_uwd(uwd, sub_kernels, domain)
        K_direct = left_kan_extension(
            (z_new, z) -> P_kernel(z_new, z) + F_kernel(z_new, z), domain)
        @test K ≈ K_direct
    end
end

@testset "Integration: compose → discretise → lambda" begin
    # Compose via UWD and check lambda matches direct computation
    full_kernel(z_new, z) = P_kernel(z_new, z) + F_kernel(z_new, z)
    A_direct = left_kan_extension(full_kernel, domain)
    λ_direct = lambda(A_direct)

    # Via compose_transitions
    A_P = left_kan_extension(P_kernel, domain)
    A_F = left_kan_extension(F_kernel, domain)
    K_composed = compose_transitions(Dict(:P => A_P, :F => A_F))
    λ_composed = lambda(K_composed)
    @test λ_composed ≈ λ_direct

    # Via oapply
    uwd = @relation (z, z_new) begin
        P(z, z_new)
        F(z, z_new)
    end
    result = oapply(uwd, [ProjectionSharer(A_P), ProjectionSharer(A_F)])
    λ_oapply = lambda(result.matrix)
    @test λ_oapply ≈ λ_direct
end

@testset "ValuedProjectionNet" begin
    @testset "Construction and accessors" begin
        vnet = ValuedProjectionNet([:seed, :small, :large],
            :survival => [(:seed => :small) => 0.2, (:small => :large) => 0.4,
                         (:small => :small) => 0.3, (:large => :large) => 0.7],
            :fecundity => [(:large => :seed) => 5.0, (:small => :seed) => 1.0])
        @test stage_names(vnet) == [:seed, :small, :large]
        @test Set(transition_names(vnet)) == Set([:survival, :fecundity])
        @test vnet.net isa LabelledProjectionNet
        @test n_states(vnet.net) == 1
        @test n_transitions(vnet.net) == 2
    end

    @testset "transition_matrix" begin
        vnet = ValuedProjectionNet([:seed, :small, :large],
            :survival => [(:seed => :small) => 0.2, (:small => :large) => 0.4,
                         (:small => :small) => 0.3, (:large => :large) => 0.7],
            :fecundity => [(:large => :seed) => 5.0, (:small => :seed) => 1.0])
        U = transition_matrix(vnet, :survival)
        @test size(U) == (3, 3)
        @test U[2, 1] ≈ 0.2   # seed → small
        @test U[3, 2] ≈ 0.4   # small → large
        @test U[2, 2] ≈ 0.3   # small → small
        @test U[3, 3] ≈ 0.7   # large → large
        @test U[1, 3] ≈ 0.0   # no fecundity here

        F = transition_matrix(vnet, :fecundity)
        @test F[1, 3] ≈ 5.0   # large → seed
        @test F[1, 2] ≈ 1.0   # small → seed
        @test all(F[2:3, :] .== 0)
    end

    @testset "to_matrix sums all transitions" begin
        vnet = ValuedProjectionNet([:seed, :small, :large],
            :survival => [(:seed => :small) => 0.2, (:small => :large) => 0.4,
                         (:small => :small) => 0.3, (:large => :large) => 0.7],
            :fecundity => [(:large => :seed) => 5.0, (:small => :seed) => 1.0])
        A = to_matrix(vnet)
        U = transition_matrix(vnet, :survival)
        F = transition_matrix(vnet, :fecundity)
        @test A ≈ U + F
    end

    @testset "Stage validation" begin
        @test_throws ArgumentError ValuedProjectionNet([:a, :b],
            :t => [(:a => :c) => 0.5])
        @test_throws ArgumentError ValuedProjectionNet([:a, :b],
            :t => [(:c => :a) => 0.5])
    end

    @testset "Unknown transition_matrix throws" begin
        vnet = ValuedProjectionNet([:a, :b],
            :t => [(:a => :b) => 0.5])
        @test_throws ArgumentError transition_matrix(vnet, :nonexistent)
    end

    @testset "Round-trip: ValuedProjectionNet matches manual matrix" begin
        A_manual = [0.0 1.0 5.0;
                    0.2 0.3 0.0;
                    0.0 0.4 0.7]
        vnet = ValuedProjectionNet([:seed, :small, :large],
            :survival => [(:seed => :small) => 0.2, (:small => :large) => 0.4,
                         (:small => :small) => 0.3, (:large => :large) => 0.7],
            :fecundity => [(:large => :seed) => 5.0, (:small => :seed) => 1.0])
        @test to_matrix(vnet) ≈ A_manual
    end
end

@testset "Lowering stubs" begin
    @test CategoricalProjectionModels.lower isa Function
    @test CategoricalProjectionModels.lift isa Function
    # Target types exist
    @test IPMTarget isa Type
    @test MPMTarget isa Type
    @test ProjectionNetTarget isa Type
end

@testset "ValuedProjectionNet lowering to MPM" begin
    vnet = ValuedProjectionNet([:seed, :small, :large],
        :survival => [(:seed => :small) => 0.2, (:small => :large) => 0.4,
                     (:small => :small) => 0.3, (:large => :large) => 0.7],
        :fecundity => [(:large => :seed) => 5.0, (:small => :seed) => 1.0])

    mpm = lower(vnet, MPMTarget())
    @test mpm isa MatrixProjectionModel
    @test size(mpm) == (3, 3)
    @test mpm.stage_names == [:seed, :small, :large]
    @test mpm.A ≈ to_matrix(vnet)
    @test lambda(mpm) > 0

    # Matches manual matrix construction
    A_manual = [0.0 1.0 5.0;
                0.2 0.3 0.0;
                0.0 0.4 0.7]
    @test mpm.A ≈ A_manual
end

include("test_time_lag.jl")

# ---------------------------------------------------------------------------
end # top-level testset
# ---------------------------------------------------------------------------
