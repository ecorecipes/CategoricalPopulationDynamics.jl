@testset "Time Lag" begin

    @testset "lag_expand LabelledProjectionNet" begin
        net = LabelledProjectionNet([:size],
            :survival_growth => (:size => :size),
            :fecundity => (:size => :size))
        lag_net = lag_expand(net, Dict(:fecundity => 1))

        # States: size_lag0, size_lag1
        @test n_states(lag_net) == 2
        state_names = sname(lag_net)
        @test :size_lag0 in state_names
        @test :size_lag1 in state_names

        # Transitions: survival_growth_lag0, fecundity_lag1, shift_size_lag0_to_1
        trans_names = tname(lag_net)
        @test :survival_growth_lag0 in trans_names
        @test :fecundity_lag1 in trans_names
        @test :shift_size_lag0_to_1 in trans_names
        @test n_transitions(lag_net) == 3
    end

    @testset "lag_expand multi-state net" begin
        net = LabelledProjectionNet([:juvenile, :adult],
            :growth => (:juvenile => :adult),
            :survival => (:adult => :adult),
            :reproduction => (:adult => :juvenile))
        lag_net = lag_expand(net, Dict(:reproduction => 1))

        # 2 states × 2 lag copies = 4 states
        @test n_states(lag_net) == 4
        state_names = sname(lag_net)
        @test :juvenile_lag0 in state_names
        @test :adult_lag0 in state_names
        @test :juvenile_lag1 in state_names
        @test :adult_lag1 in state_names

        # growth_lag0, survival_lag0, reproduction_lag1, shift_juvenile_lag0_to_1, shift_adult_lag0_to_1
        @test n_transitions(lag_net) == 5
    end

    @testset "lag_expand L=2" begin
        net = LabelledProjectionNet([:size],
            :P => (:size => :size),
            :F => (:size => :size))
        lag_net = lag_expand(net, Dict(:F => 2))

        # 1 state × 3 lag copies = 3 states
        @test n_states(lag_net) == 3
        # P_lag0, F_lag2, shift_size_lag0_to_1, shift_size_lag1_to_2
        @test n_transitions(lag_net) == 4
    end

    @testset "lag_expand validation" begin
        net = LabelledProjectionNet([:size],
            :P => (:size => :size))
        @test_throws ArgumentError lag_expand(net, Dict(:P => 0))
    end

    @testset "lag_expand ValuedProjectionNet" begin
        vnet = ValuedProjectionNet([:seed, :small, :large],
            :survival => [(:seed => :small) => 0.2, (:small => :large) => 0.4,
                         (:small => :small) => 0.3, (:large => :large) => 0.7],
            :fecundity => [(:large => :seed) => 5.0, (:small => :seed) => 1.0])

        vnet_lag = lag_expand(vnet, Dict(:fecundity => 1))

        # 3 stages × 2 lag copies = 6 expanded stages
        @test length(stage_names(vnet_lag)) == 6

        # to_matrix should produce the augmented 6×6 matrix
        A_lag = to_matrix(vnet_lag)
        @test size(A_lag) == (6, 6)

        # Top-left 3×3 block should be U (survival at lag 0)
        U = transition_matrix(vnet, :survival)
        @test A_lag[1:3, 1:3] ≈ U

        # Top-right 3×3 block should be F (fecundity at lag 1)
        F = transition_matrix(vnet, :fecundity)
        @test A_lag[1:3, 4:6] ≈ F

        # Bottom-left 3×3 block should be I (identity shifts)
        @test A_lag[4:6, 1:3] ≈ Matrix{Float64}(I, 3, 3)

        # Bottom-right 3×3 block should be 0
        @test A_lag[4:6, 4:6] ≈ zeros(3, 3)
    end

    @testset "ValuedProjectionNet lag matches expand_lag_matrix" begin
        using StructuredPopulationCore: expand_lag_matrix, TimeLagStructure

        vnet = ValuedProjectionNet([:seed, :small, :large],
            :survival => [(:seed => :small) => 0.2, (:small => :large) => 0.4,
                         (:small => :small) => 0.3, (:large => :large) => 0.7],
            :fecundity => [(:large => :seed) => 5.0, (:small => :seed) => 1.0])

        U = transition_matrix(vnet, :survival)
        F = transition_matrix(vnet, :fecundity)

        # Categorical lag expansion
        vnet_lag = lag_expand(vnet, Dict(:fecundity => 1))
        A_cat = to_matrix(vnet_lag)

        # Direct expand_lag_matrix
        A_direct = expand_lag_matrix([U, F], TimeLagStructure(1))

        @test A_cat ≈ A_direct
    end

    @testset "lag_stratify" begin
        using StructuredPopulationCore: expand_lag_matrix, TimeLagStructure

        U = [0.0 0.0; 0.5 0.3]
        F = [0.0 2.0; 0.0 0.0]
        D = [0.8 0.2; 0.3 0.7]  # 2-patch dispersal

        lag_struct = TimeLagStructure(1)
        A_ls = lag_stratify([U, F], D, lag_struct)

        # (L+1)m × (L+1)m = 4×4 lag matrix, then 2 patches → 8×8
        @test size(A_ls) == (8, 8)

        # Should equal stratify(expand_lag_matrix(...), D)
        K_lag = expand_lag_matrix([U, F], lag_struct)
        A_expected = stratify(K_lag, D)
        @test A_ls ≈ A_expected
    end

    @testset "Lag-stratification commutativity (eigenvalue)" begin
        using StructuredPopulationCore: expand_lag_matrix, TimeLagStructure

        U = [0.0 0.0; 0.5 0.3]
        F = [0.0 2.0; 0.0 0.0]
        D = [0.8 0.2; 0.3 0.7]

        lag_struct = TimeLagStructure(1)

        # Path 1: lag then stratify
        K_lag = expand_lag_matrix([U, F], lag_struct)
        A_lag_strat = stratify(K_lag, D)

        # Path 2: stratify then lag
        U_strat = stratify(U, D)
        F_strat = stratify(F, D)
        A_strat_lag = expand_lag_matrix([U_strat, F_strat], lag_struct)

        # State orderings differ (patch×lag vs lag×patch) but eigenvalues match
        λ1 = lambda(A_lag_strat)
        λ2 = lambda(A_strat_lag)
        @test λ1 ≈ λ2 atol=1e-10
    end

    @testset "Lambda of lagged ValuedProjectionNet" begin
        vnet = ValuedProjectionNet([:seed, :small, :large],
            :survival => [(:seed => :small) => 0.2, (:small => :large) => 0.4,
                         (:small => :small) => 0.3, (:large => :large) => 0.7],
            :fecundity => [(:large => :seed) => 5.0, (:small => :seed) => 1.0])

        # Standard lambda
        A_std = to_matrix(vnet)
        λ_std = lambda(A_std)

        # Lagged lambda
        vnet_lag = lag_expand(vnet, Dict(:fecundity => 1))
        A_lag = to_matrix(vnet_lag)
        λ_lag = lambda(A_lag)

        @test λ_lag > 0
        @test isfinite(λ_lag)
        # Lagged and standard should differ
        @test !isapprox(λ_lag, λ_std; atol=1e-4)
    end

end
