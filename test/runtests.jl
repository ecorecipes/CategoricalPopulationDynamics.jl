using Test
using CategoricalPopulationDynamics
using Catlab
using Catlab.CategoricalAlgebra
using Catlab.WiringDiagrams
using Catlab.Programs: @relation
import FiniteStatePopulationDynamics
using LinearAlgebra
using ContinuousStatePopulationDynamics: ContinuousIPMProblem, DelayIPMProblem,
    DelayGeneratorTerm, FixedMeshUpwind, PSPMIPMProblem, to_ode_problem, to_dde_problem,
    to_sde_problem
using MatrixProjectionModels
using StructuredPopulationCore: lambda
using Random

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
@testset "CategoricalPopulationDynamics.jl" begin
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

    @testset "Homogeneous stratification" begin
        A_strat = stratify(A_local, D)
        @test size(A_strat) == (100, 100)

        # Check block structure: top-left = 0.8 * A_local
        n = 50
        @test A_strat[1:n, 1:n] ≈ 0.8 * A_local
        @test A_strat[1:n, (n+1):2n] ≈ 0.2 * A_local
        @test A_strat[(n+1):2n, 1:n] ≈ 0.3 * A_local
        @test A_strat[(n+1):2n, (n+1):2n] ≈ 0.7 * A_local
    end

    @testset "Heterogeneous stratification" begin
        A1 = left_kan_extension(P_kernel, domain)
        A2 = 0.8 * A1  # different local matrix for patch 2

        A_het = stratify([A1, A2], D)
        n = 50
        @test size(A_het) == (100, 100)

        # Block (i,j) = D[i,j] * A_locals[j]  (source stratum's matrix)
        @test A_het[1:n, 1:n] ≈ 0.8 * A1
        @test A_het[1:n, (n+1):2n] ≈ 0.2 * A2      # source = patch 2
        @test A_het[(n+1):2n, 1:n] ≈ 0.3 * A1       # source = patch 1
        @test A_het[(n+1):2n, (n+1):2n] ≈ 0.7 * A2
    end

    @testset "Heterogeneous with identical matrices equals homogeneous" begin
        A_homo = stratify(A_local, D)
        A_het2 = stratify([A_local, A_local], D)
        @test A_homo ≈ A_het2
    end

    @testset "Heterogeneous identity coupling = block diagonal" begin
        A1 = left_kan_extension(P_kernel, domain)
        A2 = 0.5 * A1
        A_blk = stratify([A1, A2], [1.0 0.0; 0.0 1.0])
        n = 50
        @test A_blk[1:n, 1:n] ≈ A1
        @test A_blk[(n+1):2n, (n+1):2n] ≈ A2
        @test norm(A_blk[1:n, (n+1):2n]) ≈ 0.0 atol=1e-15
        @test norm(A_blk[(n+1):2n, 1:n]) ≈ 0.0 atol=1e-15
    end

    @testset "Heterogeneous dimension validation" begin
        A1 = ones(3, 3)
        A2 = ones(4, 4)
        @test_throws DimensionMismatch stratify([A1, A2], D)
        @test_throws DimensionMismatch stratify([A1, A1, A1], D)
    end

    @testset "Homogeneous dimension validation" begin
        @test_throws DimensionMismatch stratify(ones(3, 2), D)
        @test_throws DimensionMismatch stratify(ones(3, 3), [1.0 0.0 0.0; 0.0 1.0 0.0])
    end

    @testset "Process-specific coupling via compose + stratify" begin
        # Simulates the genotype-stratification pattern:
        # survival = block-diagonal, fecundity = cross-stratum
        A1 = 0.3 * ones(2, 2)
        A2 = 0.5 * ones(2, 2)
        F1 = 0.1 * ones(2, 2)
        F2 = 0.2 * ones(2, 2)

        M = [0.7 0.3; 0.4 0.6]  # coupling for fecundity only

        A_surv = stratify([A1, A2], [1.0 0.0; 0.0 1.0])
        A_fec  = stratify([F1, F2], M)
        A_full = compose_transitions(Dict(:survival => A_surv, :fecundity => A_fec))

        @test size(A_full) == (4, 4)
        # Survival blocks: diagonal only
        @test A_full[1:2, 1:2] ≈ A1 + 0.7 * F1
        @test A_full[3:4, 3:4] ≈ A2 + 0.6 * F2
        # Off-diagonal: only from fecundity coupling
        @test A_full[1:2, 3:4] ≈ 0.3 * F2
        @test A_full[3:4, 1:2] ≈ 0.4 * F1
    end
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

    @testset "merge: compose from smaller VPNs" begin
        stages = [:seed, :small, :large]
        surv = ValuedProjectionNet(stages,
            :survival => [(:seed => :small) => 0.2, (:small => :large) => 0.4,
                         (:small => :small) => 0.3, (:large => :large) => 0.7])
        fec = ValuedProjectionNet(stages,
            :fecundity => [(:large => :seed) => 5.0, (:small => :seed) => 1.0])

        full = merge(surv, fec)
        @test Set(transition_names(full)) == Set([:survival, :fecundity])
        @test to_matrix(full) ≈ to_matrix(surv) + to_matrix(fec)
        @test stage_names(full) == stages
    end

    @testset "merge: variadic (3+ nets)" begin
        stages = [:a, :b]
        n1 = ValuedProjectionNet(stages, :t1 => [(:a => :b) => 0.3])
        n2 = ValuedProjectionNet(stages, :t2 => [(:b => :a) => 0.5])
        n3 = ValuedProjectionNet(stages, :t3 => [(:a => :a) => 0.1])
        full = merge(n1, n2, n3)
        @test Set(transition_names(full)) == Set([:t1, :t2, :t3])
        @test to_matrix(full) ≈ to_matrix(n1) + to_matrix(n2) + to_matrix(n3)
    end

    @testset "merge: error on duplicate transition names" begin
        stages = [:a, :b]
        n1 = ValuedProjectionNet(stages, :t1 => [(:a => :b) => 0.3])
        n2 = ValuedProjectionNet(stages, :t1 => [(:b => :a) => 0.5])
        @test_throws ArgumentError merge(n1, n2)
    end

    @testset "merge: error on different stage names" begin
        n1 = ValuedProjectionNet([:a, :b], :t1 => [(:a => :b) => 0.3])
        n2 = ValuedProjectionNet([:x, :y], :t2 => [(:x => :y) => 0.5])
        @test_throws ArgumentError merge(n1, n2)
    end

    @testset "map_values: modify single transition" begin
        stages = [:egg, :larva, :adult]
        vnet = ValuedProjectionNet(stages,
            :survival => [(:egg => :larva) => 0.5, (:larva => :adult) => 0.3,
                         (:adult => :adult) => 0.8],
            :fecundity => [(:adult => :egg) => 10.0])

        # Halve only larval survival
        modified = map_values(vnet, :survival) do (from, to), val
            from == :larva ? val * 0.5 : val
        end
        # Larval transitions halved
        @test transition_matrix(modified, :survival)[3, 2] ≈ 0.15  # larva→adult
        # Non-larval unchanged
        @test transition_matrix(modified, :survival)[2, 1] ≈ 0.5   # egg→larva
        @test transition_matrix(modified, :survival)[3, 3] ≈ 0.8   # adult→adult
        # Fecundity untouched
        @test transition_matrix(modified, :fecundity) ≈ transition_matrix(vnet, :fecundity)
    end

    @testset "map_values: modify all transitions" begin
        stages = [:a, :b]
        vnet = ValuedProjectionNet(stages,
            :t1 => [(:a => :b) => 0.4],
            :t2 => [(:b => :a) => 2.0])
        scaled = map_values(vnet) do _, val
            0.5 * val
        end
        @test to_matrix(scaled) ≈ 0.5 * to_matrix(vnet)
    end

    @testset "merge + map_values round-trip" begin
        stages = [:egg, :larva, :adult]
        surv = ValuedProjectionNet(stages,
            :survival => [(:egg => :larva) => 0.5, (:larva => :adult) => 0.3,
                         (:adult => :adult) => 0.8])
        fec = ValuedProjectionNet(stages,
            :fecundity => [(:adult => :egg) => 10.0])

        # Build base, then modify for a "Bt" variant
        base = merge(surv, fec)
        bt_variant = map_values(base, :survival) do (from, _), val
            from == :larva ? val * 0.2 : val
        end
        # Matrix should equal modified survival + original fecundity
        A_expected = transition_matrix(bt_variant, :survival) +
                     transition_matrix(bt_variant, :fecundity)
        @test to_matrix(bt_variant) ≈ A_expected
    end

    @testset "⊕ operator" begin
        stages = [:a, :b, :c]
        s = ValuedProjectionNet(stages, :s => [(:a => :b) => 0.3, (:b => :c) => 0.4])
        f = ValuedProjectionNet(stages, :f => [(:c => :a) => 5.0])
        g = ValuedProjectionNet(stages, :g => [(:b => :a) => 1.0])
        # Binary
        @test to_matrix(s ⊕ f) ≈ to_matrix(merge(s, f))
        # Chain (left-associative)
        @test to_matrix(s ⊕ f ⊕ g) ≈ to_matrix(merge(s, f, g))
    end

    @testset "⊘ operator" begin
        vnet = ValuedProjectionNet([:a, :b],
            :t1 => [(:a => :b) => 0.4, (:b => :b) => 0.6],
            :t2 => [(:b => :a) => 2.0])
        # Scale :t1 entries where from == :a
        modified = vnet ⊘ (:t1 => ((from, _), val) -> from == :a ? val * 0.5 : val)
        expected = map_values(vnet, :t1) do (from, _), val
            from == :a ? val * 0.5 : val
        end
        @test to_matrix(modified) ≈ to_matrix(expected)
        # :t2 untouched
        @test transition_matrix(modified, :t2) ≈ transition_matrix(vnet, :t2)
    end
end

@testset "Lowering stubs" begin
    @test CategoricalPopulationDynamics.lower isa Function
    @test CategoricalPopulationDynamics.lift isa Function
    # Target types exist
    @test IPMTarget isa Type
    @test ContinuousIPMTarget isa Type
    @test PSPMTarget isa Type
    @test FiniteStateDynamicsTarget isa Type
    @test MPMTarget isa Type
    @test StateDependentMPMTarget isa Type
    @test ProjectionNetTarget isa Type
    @test ProjectionSystemNet isa Type
end

@testset "LabelledProjectionNet lowering to continuous IPM" begin
    net = LabelledProjectionNet([:size],
        :survival_growth => (:size => :size),
        :fecundity => (:size => :size))

    generator_transform = G -> begin
        G = Matrix(G)
        G .- Diagonal(vec(sum(G; dims = 1)))
    end

    target = ContinuousIPMTarget(
        :size => ContinuousProjectionDomain(0.0, 5.0, 20);
        u0 = fill(1 / 20, 20),
        tspan = (0.0, 4.0),
        source = fill(0.01, 20),
        generator_transform = generator_transform,
        normalize = false,
    )

    prob = lower(net, target, Dict(
        :survival_growth => P_kernel,
        :fecundity => F_kernel,
    ))

    @test prob isa ContinuousIPMProblem
    @test prob.tspan == (0.0, 4.0)
    @test prob.domain.n_meshpoints == 20

    base_generator = left_kan_extension((z_new, z) -> P_kernel(z_new, z) + F_kernel(z_new, z),
        ContinuousProjectionDomain(0.0, 5.0, 20))
    expected_generator = generator_transform(base_generator)
    @test prob.generator ≈ expected_generator

    odeprob = to_ode_problem(prob)
    du = zeros(20)
    odeprob.f(du, odeprob.u0, odeprob.p, 0.0)
    @test du ≈ expected_generator * prob.u0 .+ fill(0.01, 20)
end

@testset "LabelledProjectionNet lowering to PSPM IPM" begin
    net = LabelledProjectionNet([:size],
        :growth => (:size => :size),
        :mortality => (:size => :size),
        :birth => (:size => :size))

    target = PSPMTarget(
        :size => ContinuousProjectionDomain(0.0, 1.0, 3);
        u0 = [1.0, 2.0, 3.0],
        aux0 = [0.5],
        tspan = (0.0, 1.0),
        discretization = FixedMeshUpwind(),
    )

    prob = lower(net, target, Dict(
        :growth => (velocity = z -> 1.0,),
        :mortality => (mortality = (z, population, aux, p, t) -> fill(aux[1], length(z)),),
        :birth => (
            boundary_lower = (population, aux, p, t, domain) -> 0.5,
            source = 0.1,
        ),
    ))

    @test prob isa PSPMIPMProblem
    @test prob.discretization isa FixedMeshUpwind
    @test prob.aux0 == [0.5]

    odeprob = to_ode_problem(prob)
    du = zeros(4)
    odeprob.f(du, odeprob.u0, odeprob.p, 0.0)
    @test du ≈ [-1.9, -3.9, -4.4, 0.0]
end

@testset "LabelledProjectionNet lowering to delay continuous IPM" begin
    net = LabelledProjectionNet([:size],
        :survival_growth => (:size => :size),
        :fecundity => (:size => :size))

    dom = ContinuousProjectionDomain(0.0, 5.0, 10)
    n = 10
    h = 5.0 / n
    A_mat = zeros(n, n); A_mat[1, end] = 0.5      # matrix operator, used as-is
    delay_kernel(z_new, z) = 0.1                  # kernel operator, Kan-extended

    target = ContinuousIPMTarget(
        :size => dom;
        u0 = fill(1 / n, n),
        tspan = (0.0, 2.0),
        delay_terms = [DelayGeneratorTerm(1.0, A_mat), 0.5 => delay_kernel],
        history = (p, t) -> fill(0.2, n),
    )

    prob = lower(net, target, Dict(
        :survival_growth => P_kernel,
        :fecundity => F_kernel,
    ))

    @test prob isa DelayIPMProblem
    @test length(prob.delay_terms) == 2
    @test prob.delay_terms[1].lag == 1.0
    @test prob.delay_terms[1].operator == A_mat
    @test prob.delay_terms[2].lag == 0.5
    @test all(prob.delay_terms[2].operator .≈ h * 0.1)   # midpoint Kan extension

    # requires history when delay terms are present
    @test_throws ArgumentError ContinuousIPMTarget(:size => dom;
        delay_terms = [DelayGeneratorTerm(1.0, A_mat)])

    dde = to_dde_problem(prob)
    du = zeros(n)
    dde.f(du, dde.u0, dde.h, dde.p, 0.5)
    @test all(isfinite, du)
end

@testset "LabelledProjectionNet lowering to PSPM with auxiliary state" begin
    net = LabelledProjectionNet([:size],
        :growth => (:size => :size),
        :feedback => (:size => :size))

    target = PSPMTarget(
        :size => ContinuousProjectionDomain(0.0, 1.0, 2);
        u0 = [2.0, 1.0],
        aux0 = [0.5],
        tspan = (0.0, 1.0),
    )

    prob = lower(net, target, Dict(
        :growth => (velocity = 0.0,),
        :feedback => (
            auxiliary_rhs = (population, aux, p, t, domain) -> [sum(population) - aux[1]],
        ),
    ))

    @test prob isa PSPMIPMProblem
    @test prob.aux0 == [0.5]

    odeprob = to_ode_problem(prob)
    du = zeros(3)
    odeprob.f(du, odeprob.u0, odeprob.p, 0.0)
    # no transport/mortality/source -> population derivative 0;
    # aux derivative = sum(pop) - aux[1] = 3 - 0.5 = 2.5
    @test du ≈ [0.0, 0.0, 2.5]
end

@testset "Multi-state ContinuousIPMTarget lowering" begin
    net = LabelledProjectionNet([:juvenile, :adult],
        :maturation => (:juvenile => :adult),
        :adult_survival => (:adult => :adult),
        :reproduction => (:adult => :juvenile))

    djuv = ContinuousProjectionDomain(0.0, 2.0, 3)
    dad = ContinuousProjectionDomain(0.0, 4.0, 4)

    target = ContinuousIPMTarget(
        Dict(:juvenile => djuv, :adult => dad);
        tspan = (0.0, 1.0),
    )
    prob = lower(net, target, Dict(
        :maturation => (z_new, z) -> 0.3,
        :adult_survival => (z_new, z) -> 0.5,
        :reproduction => (z_new, z) -> 0.2,
    ))

    @test prob isa ContinuousIPMProblem
    N = 3 + 4
    @test size(prob.generator) == (N, N)
    @test length(prob.u0) == N

    G = prob.generator
    hj = 2.0 / 3        # source step for juvenile
    had = 4.0 / 4       # source step for adult
    # state order [:juvenile, :adult] -> blocks rows/cols 1:3 and 4:7
    @test all(G[4:7, 1:3] .≈ hj * 0.3)    # maturation juvenile -> adult
    @test all(G[4:7, 4:7] .≈ had * 0.5)   # adult_survival adult -> adult
    @test all(G[1:3, 4:7] .≈ had * 0.2)   # reproduction adult -> juvenile
    @test all(G[1:3, 1:3] .== 0.0)        # no juvenile -> juvenile transition

    odeprob = to_ode_problem(prob)
    du = zeros(N)
    odeprob.f(du, odeprob.u0, odeprob.p, 0.0)
    @test du ≈ G * odeprob.u0

    # kernel-function delay operators are rejected for multi-state targets
    bad = ContinuousIPMTarget(Dict(:juvenile => djuv, :adult => dad);
        delay_terms = [1.0 => ((z_new, z) -> 0.1)],
        history = (p, t) -> ones(N))
    @test_throws ArgumentError lower(net, bad, Dict(
        :maturation => (z_new, z) -> 0.3,
        :adult_survival => (z_new, z) -> 0.5,
        :reproduction => (z_new, z) -> 0.2))
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

@testset "ValuedProjectionNet lowering to finite-state dynamics" begin
    vnet = ValuedProjectionNet([:seed, :small, :large],
        :survival => [(:seed => :small) => 0.2, (:small => :large) => 0.4,
                     (:small => :small) => 0.3, (:large => :large) => 0.7],
        :fecundity => [(:large => :seed) => 5.0, (:small => :seed) => 1.0])

    generator_transform = G -> begin
        G = Matrix(G)
        G .- Diagonal(vec(sum(G; dims = 1)))
    end

    target = FiniteStateDynamicsTarget(;
        domain = DiscreteProjectionDomain([:seed, :small, :large]),
        u0 = [0.2, 0.3, 0.5],
        tspan = (0.0, 3.0),
        source = [0.01, 0.0, 0.0],
        generator_transform = generator_transform,
    )

    prob = lower(vnet, target)
    @test prob isa FiniteStatePopulationDynamics.FiniteStateGeneratorProblem
    @test prob.tspan == (0.0, 3.0)
    @test prob.domain.labels == [:seed, :small, :large]

    expected_generator = generator_transform(to_matrix(vnet))
    @test prob.generator ≈ expected_generator

    odeprob = FiniteStatePopulationDynamics.to_ode_problem(prob)
    du = zeros(3)
    odeprob.f(du, odeprob.u0, odeprob.p, 0.0)
    @test du ≈ expected_generator * prob.u0 .+ [0.01, 0.0, 0.0]
end

@testset "LabelledProjectionNet lowering to finite-state dynamics" begin
    net = LabelledProjectionNet([:population],
        :survival => (:population => :population),
        :fecundity => (:population => :population))

    target = FiniteStateDynamicsTarget(; tspan = (0.0, 1.0))
    prob = lower(net, target, Dict(
        :survival => [0.0 1.0; 0.2 0.3],
        :fecundity => [0.0 0.0; 0.0 0.1],
    ))

    @test prob isa FiniteStatePopulationDynamics.FiniteStateGeneratorProblem
    @test prob.domain.labels == [:state_1, :state_2]
    @test prob.u0 ≈ fill(0.5, 2)
end

@testset "Delay-aware finite-state lowering" begin
    vnet = ValuedProjectionNet([:juvenile, :adult],
        :transition => [(:juvenile => :adult) => 0.5,
                        (:adult => :adult) => -0.1,
                        (:juvenile => :juvenile) => -0.5])

    delay_matrix = [0.0 0.2; 0.0 0.0]
    history(p, t) = [0.5, 0.5]

    target = FiniteStateDynamicsTarget(;
        u0 = [1.0, 0.0],
        tspan = (0.0, 2.0),
        delay_terms = [FiniteStatePopulationDynamics.DelayGeneratorTerm(1.0, delay_matrix)],
        history = history,
    )

    prob = lower(vnet, target)
    @test prob isa FiniteStatePopulationDynamics.DelayFiniteStateProblem
    @test length(prob.delay_terms) == 1
    @test prob.delay_terms[1].lag == 1.0
    @test prob.delay_terms[1].operator ≈ delay_matrix
    @test prob.history === history

    ddeprob = FiniteStatePopulationDynamics.to_dde_problem(prob)
    @test nameof(typeof(ddeprob)) === :DDEProblem

    # Convenience `lag => operator` syntax
    target2 = FiniteStateDynamicsTarget(;
        u0 = [1.0, 0.0],
        tspan = (0.0, 1.0),
        delay_terms = [2.0 => delay_matrix],
        history = history,
    )
    prob2 = lower(vnet, target2)
    @test prob2 isa FiniteStatePopulationDynamics.DelayFiniteStateProblem
    @test prob2.delay_terms[1].lag == 2.0

    # Missing history when delay_terms is non-empty is an error
    @test_throws ArgumentError FiniteStateDynamicsTarget(;
        u0 = [1.0, 0.0],
        tspan = (0.0, 1.0),
        delay_terms = [1.0 => delay_matrix])

    # Mismatched delay operator shape is an error at lowering time
    bad_target = FiniteStateDynamicsTarget(;
        u0 = [1.0, 0.0],
        tspan = (0.0, 1.0),
        delay_terms = [FiniteStatePopulationDynamics.DelayGeneratorTerm(1.0, zeros(3, 3))],
        history = history,
    )
    @test_throws DimensionMismatch lower(vnet, bad_target)
end

@testset "Callbacks thread through categorical lowering" begin
    vnet = ValuedProjectionNet([:juvenile, :adult],
        :transition => [(:juvenile => :adult) => 0.5,
                        (:adult => :adult) => -0.1,
                        (:juvenile => :juvenile) => -0.5])

    cb = FiniteStatePopulationDynamics.scheduled_event(1.0, integ -> nothing)

    target = FiniteStateDynamicsTarget(;
        u0 = [1.0, 0.0],
        tspan = (0.0, 2.0),
        callbacks = cb,
    )
    prob = lower(vnet, target)
    @test prob isa FiniteStatePopulationDynamics.FiniteStateGeneratorProblem
    @test prob.callbacks === cb

    # Also propagates into delay-aware lowering
    delay_matrix = [0.0 0.2; 0.0 0.0]
    target_delay = FiniteStateDynamicsTarget(;
        u0 = [1.0, 0.0],
        tspan = (0.0, 2.0),
        delay_terms = [1.0 => delay_matrix],
        history = (p, t) -> [0.5, 0.5],
        callbacks = cb,
    )
    prob_delay = lower(vnet, target_delay)
    @test prob_delay isa FiniteStatePopulationDynamics.DelayFiniteStateProblem
    @test prob_delay.callbacks === cb
end

@testset "ProjectionSystemNet lowering to stateful MPM" begin
    wild = ValuedProjectionNet([:juvenile, :adult],
        :survival => [(:juvenile => :adult) => 0.4, (:adult => :adult) => 0.7],
        :fecundity => [(:adult => :juvenile) => 1.5])
    sterile = ValuedProjectionNet([:juvenile, :adult],
        :survival => [(:juvenile => :adult) => 0.2, (:adult => :adult) => 0.8])
    system = ProjectionSystemNet(:wild => wild, :sterile => sterile)

    target = StateDependentMPMTarget(
        Dict(:wild => [10.0, 2.0], :sterile => [0.0, 0.0]),
        (0, 3);
        state = (fertility_scale = 0.5,),
        rules = [ReproductionRule(:wild,
            (sys, day, p) -> get_state(sys, :fertility_scale) * sys[:wild].population[2];
            name = :wild_births)],
        events = [SingleDayRelease(:sterile, 4.0, 0; stage_idx = 2)],
        observables = [Observable(:total, (sys, day, p) -> total_population(sys))],
        metadata = Dict(
            :wild => (species = :fly, type = :wild, patch = :north),
            :sterile => (species = :fly, type = :sterile, patch = :north)))

    prob = lower(system, target)
    @test prob isa CoupledMPMProblem
    @test prob.system[:wild].species == :fly
    @test prob.system[:sterile].type == :sterile
    @test get_state(prob.system, :fertility_scale) == 0.5

    sol = solve(prob, DirectIteration())
    @test sol.retcode == :Success
    @test length(sol[:wild]) == 4
    @test length(sol[:sterile]) == 4
    @test length(sol.observables[:total]) == 4
    @test length(sol.event_log) == 1
    @test sol[:sterile][2] > sol[:sterile][1]
end

@testset "Single valued net lowering to stateful MPM" begin
    vnet = ValuedProjectionNet([:juvenile, :adult],
        :survival => [(:juvenile => :adult) => 0.3, (:adult => :adult) => 0.8],
        :fecundity => [(:adult => :juvenile) => 1.0])

    target = StateDependentMPMTarget((0, 2), :population => [5.0, 1.0])
    prob = lower(vnet, target)
    @test prob isa CoupledMPMProblem
    @test Base.collect(keys(prob.system)) == [:population]
    @test prob.system[:population].population ≈ [5.0, 1.0]
end

@testset "Hybrid lowering with substeps and component transforms" begin
    plant = ValuedProjectionNet([:vegetative, :reproductive],
        :survival => [(:vegetative => :reproductive) => 0.4, (:reproductive => :reproductive) => 0.6],
        :fecundity => [(:reproductive => :vegetative) => 1.5])

    p = (
        radiation = [6.0, 2.0],
        efficiency = 1.0,
        respiration = 0.2,
        vegetative_demand = 0.5,
        reproductive_demand = 1.5,
    )

    substeps = [
        StateUpdateSubstep(:budget, :net_supply,
            (sys, day, p) -> max(0.0, p.radiation[day + 1] * p.efficiency -
                p.respiration * total_population(sys))),
        CustomSubstep(:allocation, (sys, day, p) -> begin
            demands = [
                sys[:plant].population[1] * p.vegetative_demand,
                sys[:plant].population[2] * p.reproductive_demand,
            ]
            pool = PriorityAllocationPool(get_state(sys, :net_supply), demands,
                [:vegetative, :reproductive])
            allocations, stress = allocation_stress(pool)
            ratio = supply_demand_index(pool)
            set_state!(sys, :allocations, allocations)
            set_state!(sys, :stress, stress)
            set_state!(sys, :ratio, ratio)
            return (allocations = allocations, stress = stress, ratio = ratio)
        end),
    ]

    target = StateDependentMPMTarget(
        Dict(:plant => [5.0, 2.0]),
        (0, 2);
        p = p,
        state = (
            net_supply = 0.0,
            allocations = [0.0, 0.0],
            stress = [0.0, 0.0],
            ratio = 1.0,
        ),
        substeps = substeps,
        observables = [Observable(:ratio, (sys, day, p) -> get_state(sys, :ratio))],
        component_transforms = Dict(
            :plant => (base, sys, day, p) -> begin
                stress = get_state(sys, :stress)
                ratio = get_state(sys, :ratio)
                A = Matrix(base.A)
                A[1, 2] *= ratio
                A[2, 1] *= (1 - stress[1])
                A[2, 2] *= (1 - stress[2])
                A
            end,
        ),
    )

    prob = lower(ProjectionSystemNet(:plant => plant), target)
    sol = solve(prob, DirectIteration())

    @test sol.retcode == :Success
    @test length(sol.substep_log[:budget]) == 2
    @test length(sol.substep_log[:allocation]) == 2
    @test sol.component_matrices[:plant][1][1, 2] ≈ 1.5 * sol.substep_log[:allocation][1].ratio
    @test sol.observables[:ratio][2] ≈ sol.substep_log[:allocation][1].ratio
end

include("test_time_lag.jl")

# ---------------------------------------------------------------------------
# Timescale Nesting
# ---------------------------------------------------------------------------

@testset "Timescale Nesting" begin
    using CategoricalPopulationDynamics: ⋉

    @testset "TimescaleEmbedding construction" begin
        inner = ValuedProjectionNet([:a, :b],
            :t1 => [(:a => :b) => 0.3, (:b => :a) => 0.5, (:a => :a) => 0.4, (:b => :b) => 0.2])
        emb = TimescaleEmbedding(inner, 10, :lambda)
        @test emb.steps == 10
        @test emb.scale == 1.0
        @test_throws ArgumentError TimescaleEmbedding(inner, 0, :lambda)
        @test_throws ArgumentError TimescaleEmbedding(inner, -1, :lambda)

        emb_big = TimescaleEmbedding(inner, 2, :lambda, scale=big"0.5")
        @test emb_big.scale isa BigFloat
    end

    @testset "evaluate namespace compatibility" begin
        @test evaluate === Catlab.evaluate
    end

    @testset "evaluate: lambda" begin
        inner = ValuedProjectionNet([:a, :b],
            :t1 => [(:a => :a) => 0.5, (:b => :b) => 0.8, (:a => :b) => 0.1, (:b => :a) => 0.3])
        A = to_matrix(inner)
        λ = maximum(abs.(eigvals(A)))
        emb = TimescaleEmbedding(inner, 10, :lambda)
        @test evaluate(emb) ≈ λ^10
    end

    @testset "evaluate: survival" begin
        inner = ValuedProjectionNet([:a, :b],
            :t1 => [(:a => :a) => 0.9, (:b => :b) => 0.7, (:a => :b) => 0.05, (:b => :a) => 0.1])
        emb = TimescaleEmbedding(inner, 5, :survival)
        A = to_matrix(inner)
        Ak = A^5
        expected = sum(sum(Ak, dims=1)) / size(Ak, 2)
        @test evaluate(emb) ≈ expected
    end

    @testset "evaluate: survival rejects fecundity" begin
        reproductive = ValuedProjectionNet([:juvenile, :adult],
            :survival => [(:juvenile => :adult) => 0.4, (:adult => :adult) => 0.8],
            :fecundity => [(:adult => :juvenile) => 1.2])
        emb = TimescaleEmbedding(reproductive, 1, :survival)
        @test_throws ArgumentError evaluate(emb)
    end

    @testset "evaluate: custom function" begin
        inner = ValuedProjectionNet([:a, :b],
            :t1 => [(:a => :a) => 0.9, (:b => :b) => 0.8])
        emb = TimescaleEmbedding(inner, 5, (A, steps) -> tr(A^steps))
        A = to_matrix(inner)
        @test evaluate(emb) ≈ tr(A^5)
    end

    @testset "evaluate: with scale" begin
        inner = ValuedProjectionNet([:a, :b],
            :t1 => [(:a => :a) => 0.5, (:b => :b) => 0.8, (:a => :b) => 0.1, (:b => :a) => 0.3])
        emb = TimescaleEmbedding(inner, 10, :lambda, scale=2.5)
        A = to_matrix(inner)
        λ = maximum(abs.(eigvals(A)))
        @test evaluate(emb) ≈ 2.5 * λ^10
    end

    @testset "evaluate: overflow guard" begin
        growing = ValuedProjectionNet([:a, :b],
            :growth => [(:a => :a) => 1.1, (:b => :b) => 1.2])
        emb = TimescaleEmbedding(growing, 5000, :lambda)
        @test_throws OverflowError evaluate(emb)
    end

    @testset "nest: basic" begin
        outer = ValuedProjectionNet([:egg, :larva, :adult],
            :survival  => [(:egg => :larva) => 0.5, (:larva => :adult) => 0.3, (:adult => :adult) => 0.8],
            :fecundity => [(:adult => :egg) => 1.0])
        inner = ValuedProjectionNet([:s, :h],
            :foraging => [(:s => :h) => 0.3, (:h => :s) => 0.5, (:s => :s) => 0.5, (:h => :h) => 0.4])
        nested = nest(outer, :fecundity => TimescaleEmbedding(inner, 10, :lambda))
        @test nested isa NestableVPN
        @test length(stage_names(nested)) == 3
        A_nested = to_matrix(nested)
        A_inner = to_matrix(inner)
        λ_inner = maximum(abs.(eigvals(A_inner)))
        A_surv = transition_matrix(outer, :survival)
        A_fec  = transition_matrix(outer, :fecundity) .* λ_inner^10
        @test A_nested ≈ A_surv + A_fec
    end

    @testset "nest: error on unknown transition" begin
        outer = ValuedProjectionNet([:a, :b], :t1 => [(:a => :b) => 0.5])
        inner = ValuedProjectionNet([:x, :y], :t2 => [(:x => :y) => 0.3])
        @test_throws ArgumentError nest(outer, :nonexistent => TimescaleEmbedding(inner, 10, :lambda))
    end

    @testset "⋉ operator" begin
        outer = ValuedProjectionNet([:a, :b],
            :surv => [(:a => :a) => 0.5, (:b => :b) => 0.8],
            :fec  => [(:b => :a) => 1.0])
        inner = ValuedProjectionNet([:x, :y],
            :t => [(:x => :y) => 0.4, (:y => :x) => 0.6, (:x => :x) => 0.3, (:y => :y) => 0.2])
        nested1 = nest(outer, :fec => TimescaleEmbedding(inner, 5, :lambda))
        nested2 = outer ⋉ (:fec => TimescaleEmbedding(inner, 5, :lambda))
        @test to_matrix(nested1) ≈ to_matrix(nested2)
    end

    @testset "⋉ chaining" begin
        outer = ValuedProjectionNet([:a, :b, :c],
            :surv => [(:a => :b) => 0.5, (:b => :c) => 0.3],
            :fec  => [(:c => :a) => 1.0],
            :recr => [(:b => :a) => 1.0])
        inner1 = ValuedProjectionNet([:x, :y],
            :t => [(:x => :y) => 0.4, (:y => :x) => 0.6, (:x => :x) => 0.3, (:y => :y) => 0.2])
        inner2 = ValuedProjectionNet([:p, :q],
            :t => [(:p => :q) => 0.2, (:q => :p) => 0.8, (:p => :p) => 0.6])
        nested = outer ⋉ (:fec => TimescaleEmbedding(inner1, 5, :lambda)) ⋉
                          (:recr => TimescaleEmbedding(inner2, 3, :lambda))
        @test nested isa NestableVPN
        @test length(nested.embeddings) == 2
        @test haskey(nested.embeddings, :fec)
        @test haskey(nested.embeddings, :recr)
    end

    @testset "recursive nesting" begin
        level1 = ValuedProjectionNet([:a, :b],
            :t => [(:a => :b) => 0.3, (:b => :a) => 0.5, (:a => :a) => 0.4, (:b => :b) => 0.2])
        level2_base = ValuedProjectionNet([:x, :y],
            :surv => [(:x => :x) => 0.7, (:y => :y) => 0.6],
            :fec  => [(:y => :x) => 1.0])
        level2 = level2_base ⋉ (:fec => TimescaleEmbedding(level1, 10, :lambda))
        level3_base = ValuedProjectionNet([:p, :q],
            :growth => [(:p => :q) => 0.2, (:q => :q) => 0.5],
            :repro  => [(:q => :p) => 1.0])
        level3 = level3_base ⋉ (:repro => TimescaleEmbedding(level2, 30, :lambda))
        A3 = to_matrix(level3)
        @test size(A3) == (2, 2)
        A1 = to_matrix(level1)
        λ1 = maximum(abs.(eigvals(A1)))
        A2_eff = transition_matrix(level2_base, :surv) +
                 transition_matrix(level2_base, :fec) .* λ1^10
        λ2 = maximum(abs.(eigvals(A2_eff)))
        A3_expected = transition_matrix(level3_base, :growth) +
                      transition_matrix(level3_base, :repro) .* λ2^30
        @test A3 ≈ A3_expected
    end

    @testset "nest: preserves numeric types" begin
        inner = ValuedProjectionNet([:a],
            :t => [(:a => :a) => big"0.9"])
        outer = ValuedProjectionNet([:x, :y],
            :surv => [(:x => :x) => big"0.5"],
            :fec  => [(:y => :x) => big"1.0"])
        nested = outer ⋉ (:fec => TimescaleEmbedding(inner, 2, :lambda, scale=big"0.5"))
        A = to_matrix(nested)
        @test eltype(A) == BigFloat
    end

    @testset "⊕ with NestableVPN" begin
        surv = ValuedProjectionNet([:a, :b], :surv => [(:a => :a) => 0.5, (:b => :b) => 0.8])
        fec = ValuedProjectionNet([:a, :b], :fec => [(:b => :a) => 1.0])
        inner = ValuedProjectionNet([:x, :y],
            :t => [(:x => :y) => 0.4, (:y => :x) => 0.6, (:x => :x) => 0.3, (:y => :y) => 0.2])
        fec_nested = fec ⋉ (:fec => TimescaleEmbedding(inner, 5, :lambda))
        full = surv ⊕ fec_nested
        @test full isa NestableVPN
        @test haskey(full.embeddings, :fec)
        @test to_matrix(full) ≈ to_matrix(surv) + to_matrix(fec_nested)
    end

    @testset "⊘ with NestableVPN" begin
        outer = ValuedProjectionNet([:a, :b],
            :surv => [(:a => :a) => 0.5, (:b => :b) => 0.8],
            :fec  => [(:b => :a) => 1.0])
        inner = ValuedProjectionNet([:x, :y],
            :t => [(:x => :y) => 0.4, (:y => :x) => 0.6, (:x => :x) => 0.3, (:y => :y) => 0.2])
        nested = outer ⋉ (:fec => TimescaleEmbedding(inner, 5, :lambda))
        modified = nested ⊘ (:surv => (_, val) -> val * 0.5)
        @test haskey(modified.embeddings, :fec)
        @test transition_matrix(modified.base, :surv)[1,1] ≈ 0.25
    end
end

@testset "Demographic stochasticity lowering (phase 5)" begin
    rng = Random.Xoshiro(909)

    @testset "survival_fecundity_matrices split (move vs birth)" begin
        vnet = ValuedProjectionNet([:juv, :adult],
            :survival => [(:juv => :adult) => 0.5, (:adult => :adult) => 0.7],
            :fecundity => [(:adult => :juv) => 2.0])
        U, F = survival_fecundity_matrices(vnet; fecundity=[:fecundity])
        @test U == [0.0 0.0; 0.5 0.7]
        @test F == [0.0 2.0; 0.0 0.0]
        @test U .+ F == to_matrix(vnet)
    end

    @testset "DemographicMPMTarget -> demographic MPMProblem (discrete time)" begin
        vnet = ValuedProjectionNet([:juv, :adult],
            :survival => [(:juv => :adult) => 0.5, (:adult => :adult) => 0.7],
            :fecundity => [(:adult => :juv) => 2.0])
        A = [0.0 2.0; 0.5 0.7]
        n0 = [40, 40]
        prob = lower(vnet, DemographicMPMTarget(n0, (0, 5); fecundity=[:fecundity]))
        @test prob isa MPMProblem
        s1 = solve(prob, DirectIteration(); rng=Random.Xoshiro(1))
        @test all(x -> x == round(x) && x >= 0, s1.u[end])

        reps = 3000
        acc = [zeros(2) for _ in 1:6]
        for _ in 1:reps
            s = solve(prob, DirectIteration(); rng=rng)
            for tt in 1:6
                acc[tt] .+= s.u[tt]
            end
        end
        det = Vector{Vector{Float64}}(undef, 6); det[1] = Float64.(n0)
        for tt in 2:6
            det[tt] = A * det[tt-1]
        end
        for tt in 1:6
            @test isapprox(acc[tt] ./ reps, det[tt]; rtol=0.08)
        end
    end

    @testset "demographic_reactions: birth adds, migration moves" begin
        m, f = 0.4, 0.6
        vnet = ValuedProjectionNet([:juv, :adult],
            :maturation => [(:juv => :adult) => m],
            :fecundity => [(:adult => :juv) => f])
        sys = demographic_reactions(vnet; fecundity=[:fecundity])
        stoichs = [r.stoichiometry for r in sys.reactions]
        @test length(stoichs) == 2
        @test [1, 0] in stoichs        # birth: +juv only (parent persists)
        @test [-1, 1] in stoichs       # migration: juv -> adult
    end

    @testset "DemographicFiniteStateTarget -> CTMC, mean = exp(Gt)·n0" begin
        m, f = 0.4, 0.6
        vnet = ValuedProjectionNet([:juv, :adult],
            :maturation => [(:juv => :adult) => m],
            :fecundity => [(:adult => :juv) => f])
        n0 = [100, 50]
        prob = lower(vnet, DemographicFiniteStateTarget(n0, (0.0, 2.0); fecundity=[:fecundity]))
        @test prob isa FiniteStatePopulationDynamics.FiniteStateReactionProblem
        G = [-m f; m 0.0]
        grid = 0.0:0.5:2.0
        reps = 3000
        acc = [zeros(2) for _ in grid]
        for _ in 1:reps
            s = solve(prob, Demographic(); rng=rng, saveat=grid)
            for g in eachindex(grid)
                acc[g] .+= s.u[g]
            end
        end
        for (g, t) in enumerate(grid)
            @test isapprox(acc[g] ./ reps, exp(G .* t) * n0; rtol=0.06, atol=1.5)
        end
    end
end

@testset "Demographic lowering: continuous-state backends" begin
    rng = Random.Xoshiro(2718)

    @testset "DemographicIPMTarget -> binned demographic MPMProblem" begin
        net = LabelledProjectionNet([:size],
            :survival_growth => (:size => :size),
            :fecundity => (:size => :size))
        d = ContinuousProjectionDomain(0.0, 5.0, 30)
        z = meshpoints(d)
        n0 = round.(Int, 4 .* exp.(-((z .- 2.0) .^ 2)))
        target = DemographicIPMTarget(:size => d; n0=n0, tspan=(0, 4), fecundity=[:fecundity])
        prob = lower(net, target, Dict(:survival_growth => P_kernel, :fecundity => F_kernel))
        @test prob isa MPMProblem

        s1 = solve(prob, DirectIteration(); rng=Random.Xoshiro(3))
        @test all(x -> x == round(x) && x >= 0, s1.u[end])

        # deterministic mesh kernel K = P + F; ensemble mean total tracks deterministic total
        K = left_kan_extension(P_kernel, d) .+ left_kan_extension(F_kernel, d)
        detn = Float64.(n0); dettot = [sum(detn)]
        for _ in 1:4
            detn = K * detn; push!(dettot, sum(detn))
        end
        reps = 2500
        tot_acc = zeros(5)
        for _ in 1:reps
            s = solve(prob, DirectIteration(); rng=rng)
            for tt in 1:5
                tot_acc[tt] += sum(s.u[tt])
            end
        end
        @test isapprox(tot_acc ./ reps, dettot; rtol=0.06)
    end

    @testset "ContinuousIPMTarget output is demographic-realizable (compose)" begin
        net = LabelledProjectionNet([:size],
            :sg => (:size => :size), :fec => (:size => :size))
        target = ContinuousIPMTarget(:size => ContinuousProjectionDomain(0.0, 5.0, 8);
            u0 = fill(6, 8), tspan = (0.0, 1.0))
        prob = lower(net, target, Dict(:sg => P_kernel, :fec => F_kernel))
        @test prob isa ContinuousIPMProblem

        s = solve(prob, Demographic(); rng=rng, saveat=0.5)   # exact jump realization
        @test all(x -> x == round(x) && x >= 0, s.u[end])

        sde = to_sde_problem(prob)                            # chemical Langevin SDE
        u = Float64.(prob.u0); du1 = zeros(8); du2 = zeros(8)
        sde.f.f(du1, u, prob.p, 0.0)
        to_ode_problem(prob).f(du2, u, prob.p, 0.0)
        @test isapprox(du1, du2; atol=1e-10)                  # SDE drift = deterministic RHS
    end

    @testset "PSPMTarget output is demographic-realizable (SDE)" begin
        net = LabelledProjectionNet([:size],
            :growth => (:size => :size), :mortality => (:size => :size))
        target = PSPMTarget(:size => ContinuousProjectionDomain(0.0, 1.0, 4);
            u0 = [5.0, 5.0, 5.0, 5.0], tspan = (0.0, 1.0))
        prob = lower(net, target, Dict(
            :growth => (velocity = 0.3,),
            :mortality => (mortality = 0.1,)))
        @test prob isa PSPMIPMProblem

        sde = to_sde_problem(prob)
        u = prob.n0; du1 = zeros(4); du2 = zeros(4)
        sde.f.f(du1, u, prob.p, 0.0)
        to_ode_problem(prob).f(du2, u, prob.p, 0.0)
        @test isapprox(du1, du2; atol=1e-10)                  # SDE drift = transport RHS
    end
end

# ---------------------------------------------------------------------------
end # top-level testset
# ---------------------------------------------------------------------------
