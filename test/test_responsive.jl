# Stage durations, stratification of named nets, responsive nets and pooled systems.

# Loaded here rather than with the other packages: its Catlab extension adds a method of
# `coarsen` for `(::Matrix, ::FinFunction)` that would take over from this package's in the
# coarsening tests of runtests.jl, which run before this file.
import IntegralProjectionModels

# Two layouts of states are the same if they have the same names, levels and meshes
# (`DiscreteDomain` compares its levels by identity).
same_layout(a::NamedTuple, b::NamedTuple) = keys(a) == keys(b) &&
    all(x isa StructuredPopulationCore.DiscreteDomain ? (y isa StructuredPopulationCore.DiscreteDomain && x.labels == y.labels) : x == y
        for (x, y) in zip(values(a), values(b)))

@testset "expand_stage" begin
    life = ValuedProjectionNet([:egg, :larva, :adult],
        :hatching => [(:egg => :larva) => 0.5],
        :maturing => [(:larva => :adult) => 0.4],
        :surviving => [(:adult => :adult) => 0.8],
        :laying => [(:adult => :egg) => 10.0])
    daily = expand_stage(life, :egg, 3; ageing = 0.9)
    @test stage_names(daily) == [:egg1, :egg2, :egg3, :larva, :adult]
    @test :egg_ageing in transition_names(daily)
    A = to_matrix(daily)
    @test A == [0 0 0 0 10.0;
                0.9 0 0 0 0;
                0 0.9 0 0 0;
                0 0 0.5 0 0;
                0 0 0 0.4 0.8]
    # per-step ageing values, and several stages at once
    v = expand_stage(life, :larva, 3; ageing = [0.7, 0.6], name = :larval_growth)
    @test transition_matrix(v, :larval_growth)[3:4, 2:3] == [0.7 0; 0 0.6]
    both = expand_stages(life, :egg => 3, :larva => 2; ageing = Dict(:egg => 0.9))
    @test stage_names(both) == [:egg1, :egg2, :egg3, :larva1, :larva2, :adult]
    @test to_matrix(both)[5, 4] == 1.0 && to_matrix(both)[2, 1] == 0.9
    # three ageing steps plus the four original transitions
    @test count(!iszero, to_matrix(both)) == 7
    @test_throws ArgumentError expand_stage(life, :adult, 3)       # adults persist in place
    @test_throws ArgumentError expand_stage(life, :pupa, 3)
    @test_throws ArgumentError expand_stage(life, :egg, 1)
    @test_throws DimensionMismatch expand_stage(life, :egg, 3; ageing = [0.9])
    @test_throws ArgumentError expand_stage(life, :egg, 3; name = :laying)
end

@testset "stratify a valued net" begin
    life = ValuedProjectionNet([:juvenile, :adult],
        :maturing => [(:juvenile => :adult) => 0.3],
        :surviving => [(:adult => :adult) => 0.5],
        :breeding => [(:adult => :juvenile) => 2.0])
    two = stratify(life, [:north, :south])
    @test stage_names(two) == [:juvenile_north, :adult_north, :juvenile_south, :adult_south]
    @test Set(transition_names(two)) == Set([:maturing_north, :maturing_south, :surviving_north,
                                             :surviving_south, :breeding_north, :breeding_south])
    @test to_matrix(two) == stratify(to_matrix(life), Matrix(1.0I, 2, 2))

    D = [0.9 0.2; 0.1 0.8]
    mixed = stratify(life, [:north, :south]; coupling = Dict(:breeding => D))
    @test :breeding_north_to_south in transition_names(mixed)
    @test :breeding_south_to_north in transition_names(mixed)
    expected = stratify(transition_matrix(life, :maturing), Matrix(1.0I, 2, 2)) +
               stratify(transition_matrix(life, :surviving), Matrix(1.0I, 2, 2)) +
               stratify(transition_matrix(life, :breeding), D)
    @test to_matrix(mixed) ≈ expected
    # one-way coupling adds only the one cross-stratum transition
    oneway = stratify(life, [:healthy, :infected]; coupling = Dict(:maturing => [1.0 0; 1.0 1.0]))
    @test :maturing_healthy_to_infected in transition_names(oneway)
    @test !(:maturing_infected_to_healthy in transition_names(oneway))
    @test stratum_stage(:adult, :infected) == :adult_infected
    @test stratum_transition(:maturing, :healthy, :infected) == :maturing_healthy_to_infected
    @test stratum_transition(:maturing, :healthy, :healthy) == :maturing_healthy
    @test_throws ArgumentError stratify(life, [:a, :a])
    @test_throws ArgumentError stratify(life, [:a, :b]; coupling = Dict(:missing => D))
    @test_throws DimensionMismatch stratify(life, [:a, :b]; coupling = Dict(:breeding => ones(3, 3)))
end

@testset "responsive nets" begin
    K = 1000.0
    life = ValuedProjectionNet([:juvenile, :adult],
        :maturing => [(:juvenile => :adult) => 0.3],
        :surviving => [(:adult => :adult) => 0.5],
        :breeding => [(:adult => :juvenile) => 6.0])
    crowding(ctx) = max(0.0, 1 - ctx.pool.space / K)
    plant = births(respond(life, :breeding => crowding), :breeding)
    @test plant isa ResponsiveProjectionNet
    @test stage_names(plant) == [:juvenile, :adult] && to_matrix(plant) == to_matrix(life)

    ctx = context(plant, [10.0, 20.0], (space = 400.0,), nothing)
    @test ctx.n[:adult] == 20.0 && ctx.n[2] == 20.0 && ctx.pool.space == 400.0
    @test to_matrix(plant, ctx) ≈ [0 3.6; 0.3 0.5]
    U, F = survival_fecundity_matrices(plant, ctx)
    @test U == [0 0; 0.3 0.5] && F ≈ [0 3.6; 0 0]
    frozen = evaluate(plant, ctx)
    @test frozen isa ValuedProjectionNet && to_matrix(frozen) ≈ to_matrix(plant, ctx)
    @test transition_matrix(frozen, :breeding) ≈ [0 3.6; 0 0]

    # responses multiply, and may scale entries individually
    twice = respond(plant, :breeding => ctx -> 0.5, :surviving => ctx -> ((from, to) -> from === :adult ? 0.1 : 1.0))
    @test to_matrix(twice, ctx) ≈ [0 1.8; 0.3 0.05]
    @test_throws ArgumentError respond(life, :flying => ctx -> 1.0)

    # modules combine, carrying their responses
    survive = ValuedProjectionNet([:juvenile, :adult], :maturing => [(:juvenile => :adult) => 0.3],
                                  :surviving => [(:adult => :adult) => 0.5])
    breed = respond(ValuedProjectionNet([:juvenile, :adult], :breeding => [(:adult => :juvenile) => 6.0]),
                    :breeding => crowding)
    @test to_matrix(survive ⊕ breed, ctx) ≈ to_matrix(plant, ctx)
    @test to_matrix(merge(breed, survive), ctx) ≈ to_matrix(plant, ctx)

    # refining the life cycle keeps the responses, and old names still work as totals
    aged = expand_stage(plant, :juvenile, 3; ageing = 0.9)
    c3 = context(aged, [1.0, 2.0, 3.0, 20.0], (space = 400.0,), nothing)
    @test c3.n[:juvenile] == 6.0 && c3.n[:juvenile2] == 2.0 && c3.n[:adult] == 20.0
    @test to_matrix(aged, c3)[1, 4] ≈ 3.6
    strat = stratify(aged, [:healthy, :infected]; coupling = Dict(:maturing => [1.0 0; 0.5 1.0]))
    c8 = context(strat, collect(1.0:8.0), (space = 400.0,), nothing)
    @test c8.n[:adult] == 4.0 + 8.0 && c8.n[:adult_infected] == 8.0
    @test c8.n[:juvenile] == 1 + 2 + 3 + 5 + 6 + 7 && c8.n[:juvenile_healthy] == 6.0
    @test c8.n[:infected] == 5 + 6 + 7 + 8 && c8.n[:juvenile2_infected] == 6.0
    As = to_matrix(strat, c8)
    @test As[1, 4] ≈ 3.6 && As[5, 8] ≈ 3.6               # breeding responds in both strata
    @test As[8, 3] ≈ 0.15                                 # healthy juveniles maturing into the infected stratum
    @test :breeding_infected in strat.fecundity
    @test As ≈ sum(survival_fecundity_matrices(strat, c8))

    # inflows and after-step maps
    seeded = after_step(inflow(plant, :juvenile => ctx -> 0.01 * ctx.pool.space), n -> floor.(n))
    sys = PooledProjectionSystem(:plant => seeded; pools = [Pool(:space, :plant => [:adult => 1.0])])
    next = advance(sys, Dict(:plant => [10.0, 400.0]), nothing)
    @test next[:plant] == floor.([0 6.0 * (1 - 400.0 / K); 0.3 0.5] * [10.0, 400.0] .+ [4.0, 0.0])
    @test stage_names(expand_stage(seeded, :juvenile, 2)) == [:juvenile1, :juvenile2, :adult]
    @test first(expand_stage(seeded, :juvenile, 2).inflows).first == :juvenile1
    @test first(stratify(seeded, [:a, :b]).inflows).first == :juvenile_a
end

@testset "matrix-valued responses" begin
    life = ValuedProjectionNet([:egg, :juvenile, :adult],
        :hatching => [(:egg => :juvenile) => 0.5],
        :maturing => [(:juvenile => :adult) => 0.3],
        :surviving => [(:juvenile => :juvenile) => 0.2, (:adult => :adult) => 0.5],
        :breeding => [(:adult => :egg) => 6.0])
    position = Dict(:egg => 1, :juvenile => 2, :adult => 3)
    M = [0.9 0.6 0.4; 0.7 0.8 0.3; 0.2 0.1 0.5]            # M[to, from], like the projection matrix
    by_matrix = respond(life, :surviving => ctx -> M, :hatching => ctx -> M,
                        :breeding => ctx -> ctx.pool.space .* M)
    by_name = respond(life, :surviving => ctx -> ((from, to) -> M[position[to], position[from]]),
                      :hatching => ctx -> ((from, to) -> M[position[to], position[from]]),
                      :breeding => ctx -> ((from, to) -> ctx.pool.space * M[position[to], position[from]]))
    ctx = context(by_matrix, [10.0, 20.0, 30.0], (space = 0.5,), nothing)
    A = to_matrix(by_matrix, ctx)
    @test A == [0 0 6.0 * (0.5 * 0.4); 0.5 * 0.7 0.2 * 0.8 0; 0 0.3 0.5 * 0.5]
    @test A == to_matrix(by_name, ctx)
    @test survival_fecundity_matrices(births(by_matrix, :breeding), ctx) ==
          survival_fecundity_matrices(births(by_name, :breeding), ctx)
    frozen = evaluate(by_matrix, ctx)
    @test frozen isa ValuedProjectionNet && to_matrix(frozen) == A
    @test transition_matrix(frozen, :breeding) == transition_matrix(evaluate(by_name, ctx), :breeding)
    @test transition_matrix(frozen, :maturing) == transition_matrix(life, :maturing)

    # the three kinds of response multiply
    mixed = respond(by_matrix, :breeding => ctx -> 0.5, :breeding => ctx -> ((from, to) -> 2.0))
    @test to_matrix(mixed, ctx) == A
    # a response scales the entries of its transition; it does not add entries
    @test to_matrix(respond(life, :maturing => ctx -> fill(2.0, 3, 3)), ctx) == [0 0 6.0; 0.5 0.2 0; 0 0.3 * 2.0 0.5]
    # any AbstractMatrix will do
    @test to_matrix(respond(life, :surviving => ctx -> Diagonal([7.0, 3.0, 0.5])), ctx) ==
          [0 0 6.0; 0.5 0.2 * 3.0 0; 0 0.3 0.5 * 0.5]
    @test to_matrix(respond(life, :breeding => ctx -> transpose(M)), ctx)[1, 3] == 6.0 * M[3, 1]
    # the matrix must be laid out over the stages of the net
    @test_throws DimensionMismatch to_matrix(respond(life, :breeding => ctx -> ones(2, 2)), ctx)
    @test_throws DimensionMismatch evaluate(respond(life, :breeding => ctx -> ones(3, 4)), ctx)
    @test_throws ArgumentError to_matrix(respond(life, :breeding => ctx -> [1.0, 2.0, 3.0]), ctx)

    # modules combine, carrying their matrices
    rest = ValuedProjectionNet([:egg, :juvenile, :adult], :maturing => [(:juvenile => :adult) => 0.3],
        :surviving => [(:juvenile => :juvenile) => 0.2, (:adult => :adult) => 0.5])
    start = respond(ValuedProjectionNet([:egg, :juvenile, :adult], :hatching => [(:egg => :juvenile) => 0.5],
        :breeding => [(:adult => :egg) => 6.0]), :hatching => ctx -> M, :breeding => ctx -> ctx.pool.space .* M)
    @test to_matrix(respond(rest, :surviving => ctx -> M) ⊕ start, ctx) == A

    # Refining the life cycle keeps a matrix written for the unrefined one: every entry takes the factor of
    # the entry it derives from. Eggs now last three steps.
    aged = expand_stage(by_matrix, :egg, 3; ageing = 0.9)
    @test stage_names(aged) == [:egg1, :egg2, :egg3, :juvenile, :adult]
    c5 = context(aged, collect(1.0:5.0), (space = 0.5,), nothing)
    expected = zeros(5, 5)
    expected[2, 1] = expected[3, 2] = 0.9                   # ageing: no response
    expected[4, 3] = 0.5 * M[2, 1]                          # hatching, now from the last egg class
    expected[5, 4] = 0.3                                    # maturing: no response
    expected[4, 4], expected[5, 5] = 0.2 * M[2, 2], 0.5 * M[3, 3]
    expected[1, 5] = 6.0 * (0.5 * M[1, 3])                  # breeding, now into the first egg class
    @test to_matrix(aged, c5) == expected
    @test to_matrix(evaluate(aged, c5)) == expected
    # a response attached to the refined net is laid out over the refined stages
    slower = respond(aged, :egg_ageing => ctx -> fill(0.5, 5, 5))
    @test to_matrix(slower, c5)[2, 1] == 0.9 * 0.5 && to_matrix(slower, c5)[1, 5] == expected[1, 5]
    @test_throws DimensionMismatch to_matrix(respond(aged, :egg_ageing => ctx -> fill(0.5, 3, 3)), c5)

    # ... and then replicated across two strata, with half of the hatchlings of healthy eggs infected
    C = [1.0 0.0; 0.5 1.0]
    strat = stratify(aged, [:healthy, :infected]; coupling = Dict(:hatching => C))
    c10 = context(strat, collect(1.0:10.0), (space = 0.5,), nothing)
    hatching = transition_matrix(evaluate(aged, c5), :hatching)
    @test to_matrix(strat, c10) ≈ kron(Matrix(1.0I, 2, 2), expected - hatching) + kron(C, hatching)
    @test to_matrix(strat, c10)[9, 3] == 0.5 * 0.5 * M[2, 1]   # healthy egg3 to infected juvenile
    @test to_matrix(strat, c10) ≈ sum(survival_fecundity_matrices(births(strat, :breeding_healthy, :breeding_infected), c10))
    # the other way round: strata first, then age classes in one of them
    other = expand_stage(stratify(by_matrix, [:healthy, :infected]), :egg_infected, 2)
    @test stage_names(other) == [:egg_healthy, :juvenile_healthy, :adult_healthy, :egg_infected1, :egg_infected2,
                                 :juvenile_infected, :adult_infected]
    c7 = context(other, collect(1.0:7.0), (space = 0.5,), nothing)
    B = to_matrix(other, c7)
    @test B[2, 1] == 0.5 * M[2, 1] && B[6, 5] == 0.5 * M[2, 1] && B[5, 4] == 1.0
    @test B[1, 3] == 6.0 * (0.5 * M[1, 3]) && B[4, 7] == 6.0 * (0.5 * M[1, 3]) && B[7, 7] == 0.5 * M[3, 3]
    # a matrix of the wrong size is reported against the stages the response was written for
    wrong = expand_stage(respond(life, :breeding => ctx -> ones(2, 2)), :egg, 3)
    @test_throws DimensionMismatch to_matrix(wrong, c5)
    # A function of stage names is called with the names its stages had when the response was attached, so
    # one written for the simple life cycle keeps working once the life cycle is refined
    named = respond(life, :surviving => ctx -> ((from, to) -> from === :adult ? 0.1 : 1.0), :breeding => ctx -> 0.5)
    strata = stratify(named, [:healthy, :infected])
    c6 = context(strata, ones(6), (space = 0.5,), nothing)
    N = to_matrix(strata, c6)
    @test N[3, 3] ≈ 0.05 && N[6, 6] ≈ 0.05 && N[2, 2] == 0.2 && N[5, 5] == 0.2     # adults, in both strata
    @test N[1, 3] == 3.0 && N[4, 6] == 3.0
    @test to_matrix(evaluate(strata, c6)) == N
    # through two refinements, for the entries that expand_stage moves to the first and last age class
    by_stage = respond(life, :hatching => ctx -> ((from, to) -> from === :egg && to === :juvenile ? 0.5 : 2.0),
                       :breeding => ctx -> ((from, to) -> to === :egg ? 0.25 : 1.0))
    refined = stratify(expand_stage(by_stage, :egg, 3), [:a, :b])
    R = to_matrix(refined, context(refined, ones(10), (space = 0.5,), nothing))
    @test R[4, 3] == 0.25 && R[9, 8] == 0.25             # hatching, 0.5 * 0.5: from the last egg class
    @test R[1, 5] == 1.5 && R[6, 10] == 1.5              # breeding, 6.0 * 0.25: into the first egg class
    plain = stratify(expand_stage(respond(life, :hatching => ctx -> 0.5, :breeding => ctx -> 0.25), :egg, 3), [:a, :b])
    @test R == to_matrix(plain, context(plain, ones(10), (space = 0.5,), nothing))
    # a response attached after the refinement sees the refined names
    late = respond(strata, :surviving_infected => ctx -> ((from, to) -> from === :adult_infected ? 0.5 : 1.0))
    L = to_matrix(late, context(late, ones(6), (space = 0.5,), nothing))
    @test L[6, 6] ≈ 0.025 && L[3, 3] ≈ 0.05 && L[5, 5] == 0.2
    # the same response wrapped by another function, as a community does to rename pools, and refined again
    wrapped = ResponsiveProjectionNet(strata.base; responses = [t => (ctx -> f(ctx)) for (t, f) in strata.responses],
                                      groups = strata.groups)
    twice = expand_stage(wrapped, :egg_healthy, 2)
    @test stage_names(twice)[[1, 2, 4, 7]] == [:egg_healthy1, :egg_healthy2, :adult_healthy, :adult_infected]
    T2 = to_matrix(twice, context(twice, ones(7), (space = 0.5,), nothing))
    @test T2[4, 4] ≈ 0.05 && T2[7, 7] ≈ 0.05 && T2[3, 3] == 0.2 && T2[6, 6] == 0.2 && T2[1, 4] == 3.0

    # in a pooled system, natively and through the solver
    pools = [Pool(:space, :plant => [:adult => 0.01])]
    sys_matrix = PooledProjectionSystem(:plant => births(by_matrix, :breeding); pools)
    sys_name = PooledProjectionSystem(:plant => births(by_name, :breeding); pools)
    state = Dict(:plant => [10.0, 20.0, 30.0])
    a = trajectory(sys_matrix, state, fill(nothing, 30))
    b = trajectory(sys_name, state, fill(nothing, 30))
    @test all(a.states[k][:plant] == b.states[k][:plant] for k in 1:31)
    @test a.states[31][:plant] != state[:plant] && all(isfinite, a.states[31][:plant])
    sol = solve(lower(sys_matrix, StateDependentMPMTarget(state, (0, 30); p = nothing)), DirectIteration())
    @test all(sol.u[k][:plant] == a.states[k][:plant] for k in 1:31)
end

@testset "pooled systems" begin
    K = 1000.0
    crowding(ctx) = max(0.0, 1 - ctx.pool.space / K)
    grass = respond(ValuedProjectionNet([:seedling, :adult],
            :establishing => [(:seedling => :adult) => 0.30],
            :persisting => [(:adult => :adult) => 0.50],
            :seeding => [(:adult => :seedling) => 6.0]), :seeding => crowding)
    shrub = respond(ValuedProjectionNet([:seedling, :juvenile, :adult],
            :establishing => [(:seedling => :juvenile) => 0.30],
            :maturing => [(:juvenile => :adult) => 0.50],
            :persisting => [(:adult => :adult) => 0.95],
            :seeding => [(:adult => :seedling) => 3.0]), :seeding => crowding)
    space = Pool(:space, :grass => [:seedling => 0.1, :adult => 1.0], :shrub => [0.1, 1.0, 4.0])
    com = PooledProjectionSystem(:grass => grass, :shrub => shrub; pools = [space])
    @test component_names(com) == [:grass, :shrub] && pool_names(com) == [:space]
    @test stage_names(com, :shrub) == [:seedling, :juvenile, :adult]

    state = Dict(:grass => [50.0, 10.0], :shrub => [5.0, 0.0, 1.0])
    @test pool_totals(com, state, nothing).space ≈ 0.1 * 50 + 10 + 0.1 * 5 + 4
    c = 1 - 19.5 / K
    next = advance(com, state, nothing)
    @test next[:grass] ≈ [6.0 * c * 10, 0.3 * 50 + 0.5 * 10]
    @test next[:shrub] ≈ [3.0 * c * 1, 0.3 * 5, 0.95 * 1]

    out = trajectory(com, state, fill(nothing, 400))
    @test length(out.states) == 401 && length(out.pools) == 400
    final = out.states[end]
    # the shrub replaces itself at crowding 1/9, the grass needs 1/3.6: the shrub wins
    @test pool_totals(com, final, nothing).space ≈ K * (1 - 1 / 9) rtol = 1e-6
    @test sum(final[:grass]) < 1e-6

    # contributions: a number, a function of stages and environment
    counts = Pool(:individuals, :grass => 1.0, :shrub => (n, env) -> env * n[:adult])
    sys2 = PooledProjectionSystem(:grass => grass, :shrub => shrub; pools = [space, counts])
    @test pool_totals(sys2, state, 2.0).individuals == 60.0 + 2.0
    @test_throws ArgumentError PooledProjectionSystem(:grass => grass; pools = [Pool(:space, :shrub => 1.0)])
    @test_throws DimensionMismatch PooledProjectionSystem(:grass => grass; pools = [Pool(:space, :grass => [1.0])])
    @test_throws ArgumentError PooledProjectionSystem(:grass => grass, :grass => grass)

    @testset "lowering to MatrixProjectionModels" begin
        target = StateDependentMPMTarget(state, (0, 400); p = nothing)
        prob = lower(com, target)
        @test prob isa CoupledMPMProblem
        sol = solve(prob, DirectIteration())
        for k in (1, 2, 50, 401), name in (:grass, :shrub)
            @test sol.u[k][name] == out.states[k][name]
        end
        @test sol.substep_log[:pools][1].space == out.pools[1].space
        @test sol.substep_log[:pools][400].space == out.pools[400].space
        # the component's model is a MatrixProjectionModel with births kept apart
        marked = PooledProjectionSystem(:grass => births(grass, :seeding), :shrub => shrub; pools = [space])
        sol2 = solve(lower(marked, target), DirectIteration())
        @test sol2.u[401][:shrub] == out.states[401][:shrub]

        # environments, inflows and after-step maps go through the solver too
        seasonal = respond(grass, :persisting => ctx -> ctx.env ? 0.5 : 1.0)
        rain = after_step(inflow(seasonal, :seedling => ctx -> 2.0), n -> [x < 1 ? 0.0 : x for x in n])
        sys3 = PooledProjectionSystem(:grass => rain, :shrub => shrub; pools = [space])
        envs = [isodd(t) for t in 1:60]
        native = trajectory(sys3, state, envs)
        lowered = solve(lower(sys3, StateDependentMPMTarget(state, (0, 60); p = envs)), DirectIteration())
        for k in 1:61, name in (:grass, :shrub)
            @test lowered.u[k][name] ≈ native.states[k][name] rtol = 1e-13
        end
        @test_throws ArgumentError lower(com, StateDependentMPMTarget(Dict(:grass => [1.0, 1.0]), (0, 5)))
    end

    @testset "lowering to IntegralProjectionModels" begin
        IPM = IntegralProjectionModels
        SPC = StructuredPopulationCore
        # a species whose plants are in three size classes of a continuous trait, beside a seed bank
        d = SPC.ContinuousDomain(0.0, 3.0, 3)
        sized_base = ValuedProjectionNet([:seed, :z1, :z2, :z3],
            :growing => [(:z1 => :z2) => 0.5, (:z2 => :z3) => 0.5, (:z3 => :z3) => 0.8],
            :sprouting => [(:seed => :z1) => 0.2, (:seed => :seed) => 0.3],
            :seeding => [(:z3 => :seed) => 4.0])
        sized = births(respond(ResponsiveProjectionNet(sized_base; meshes = [(name = :size, domain = d, cells = [:z1, :z2, :z3])]),
                               :seeding => crowding), :seeding)
        @test same_layout(state_layout(sized), (seed = SPC.DiscreteDomain([:seed]), size = d))
        seasonal = respond(grass, :persisting => ctx -> ctx.env ? 0.5 : 1.0)
        rain = after_step(inflow(seasonal, :seedling => ctx -> 2.0), n -> [x < 1 ? 0.0 : x for x in n])
        space4 = Pool(:space, :grass => [:seedling => 0.1, :adult => 1.0], :shrub => [0.1, 1.0, 4.0], :sized => [0.0, 0.5, 1.0, 2.0])
        sys4 = PooledProjectionSystem(:grass => births(rain, :seeding), :shrub => births(shrub, :seeding), :sized => sized;
                                      pools = [space4])
        state4 = Dict(:grass => [50.0, 10.0], :shrub => [5.0, 0.0, 1.0], :sized => [10.0, 4.0, 2.0, 1.0])
        envs = [isodd(t) for t in 1:60]

        # the same system under both targets: the same steps, to the last bit
        a = solve(lower(sys4, StateDependentMPMTarget(state4, (0, 60); p = envs)), DirectIteration())
        prob = lower(sys4, CoupledIPMTarget(state4, (0, 60); p = envs))
        @test prob isa IPM.CoupledIPMProblem && isempty(prob.inflows)
        b = IPM.solve(prob, IPM.DirectIteration())
        @test b.u == a.u
        @test b.substep_log == a.substep_log && b.rule_log == a.rule_log
        @test b.component_matrices == a.component_matrices
        SPC.set_state!(prob.system, :pools, (space = 10.0,))
        kernel = prob.system[:sized].model(prob.system, 0, envs)
        @test kernel isa IPM.DiscretizedKernel && same_layout(kernel.states, state_layout(sized))
        @test CoupledIPMTarget((0, 3), :grass => [1.0, 2.0]).stochasticity isa SPC.Deterministic
        @test_throws ArgumentError CoupledIPMTarget((0, 3), :grass => [1.0, 2.0]; stochasticity = SPC.StochasticKernelResampled())
        @test_throws ArgumentError lower(com, CoupledIPMTarget(Dict(:grass => [1.0, 1.0]), (0, 5)))

        # whole individuals: for each component in turn, survival and births, then Poisson inflows, then the maps
        whole = Dict(k => round.(v) for (k, v) in state4)
        demographic = lower(sys4, CoupledIPMTarget(whole, (0, 30); p = envs, stochasticity = SPC.Demographic()))
        @test collect(keys(demographic.inflows)) == [:grass]
        x = IPM.solve(demographic; rng = Xoshiro(5))
        rng = Xoshiro(5)
        current = Dict(k => copy(v) for (k, v) in whole)
        for k in 1:30
            pool = pool_totals(sys4, current, envs[k])
            next = Dict{Symbol, Vector{Float64}}()
            for name in component_names(sys4)
                net = sys4[name]
                ctx = context(net, current[name], pool, envs[k])
                U, F = survival_fecundity_matrices(net, ctx)
                drawn = Float64.(SPC.demographic_step!(rng, zeros(Int, length(current[name])), round.(Int, current[name]), U, F))
                for (i, r) in enumerate(CategoricalPopulationDynamics._inflows(net, ctx))
                    r > 0 && (drawn[i] += SPC.rand_poisson(rng, r))
                end
                next[name] = collect(Float64, CategoricalPopulationDynamics._after(net, drawn))
            end
            current = next
            @test all(x.u[k + 1][name] == current[name] for name in component_names(sys4))
        end
    end
end

@testset "meshes" begin
    SPC = StructuredPopulationCore
    d = SPC.ContinuousDomain(0.0, 3.0, 3)
    base = ValuedProjectionNet([:seed, :z1, :z2, :z3],
        :growing => [(:z1 => :z2) => 0.5, (:z2 => :z3) => 0.5, (:z3 => :z3) => 0.8],
        :sprouting => [(:seed => :z1) => 0.2],
        :seeding => [(:z3 => :seed) => 4.0])
    net = ResponsiveProjectionNet(base; meshes = [(name = :size, domain = d, cells = [:z1, :z2, :z3])])
    @test meshes(net) == [(name = :size, domain = d, cells = [:z1, :z2, :z3])]
    @test isempty(meshes(base)) && isempty(meshes(ResponsiveProjectionNet(base)))
    @test to_matrix(net) == to_matrix(base)                                       # metadata only
    # carried by the verbs, by ⊕ and through refinement
    @test meshes(births(respond(net, :growing => ctx -> 1.0), :seeding)) == meshes(net)
    @test meshes(after_step(inflow(net, :seed => ctx -> 1.0), identity)) == meshes(net)
    dying = ResponsiveProjectionNet(ValuedProjectionNet([:seed, :z1, :z2, :z3], :dying => [(:z1 => :z1) => 0.1]))
    @test meshes(net ⊕ dying) == meshes(net) && meshes(dying ⊕ net) == meshes(net)
    @test meshes(expand_stage(net, :seed, 2)) == meshes(net)
    @test meshes(expand_stages(net, :seed => 3)) == meshes(net)
    @test isempty(meshes(expand_stage(net, :z2, 2)))                              # its cells are no longer one stage each
    two = stratify(net, [:north, :south])
    @test [m.name for m in meshes(two)] == [:size_north, :size_south]
    @test meshes(two)[2].cells == [:z1_south, :z2_south, :z3_south] && meshes(two)[2].domain == d
    @test same_layout(state_layout(two), (seed_north = SPC.DiscreteDomain([:seed_north]), size_north = d,
                                          seed_south = SPC.DiscreteDomain([:seed_south]), size_south = d))
    @test keys(state_layout(stratify(two, [:young, :old]))) ==
          (:seed_north_young, :size_north_young, :seed_south_young, :size_south_young,
           :seed_north_old, :size_north_old, :seed_south_old, :size_south_old)
    # a mesh must have one cell per mesh point, each a stage; one whose cells are not consecutive is no state
    @test_throws ArgumentError ResponsiveProjectionNet(base; meshes = [(name = :size, domain = d, cells = [:z1, :z2])])
    @test_throws ArgumentError ResponsiveProjectionNet(base; meshes = [(name = :size, domain = d, cells = [:z1, :z2, :w])])
    shuffled = ResponsiveProjectionNet(base; meshes = [(:size, d, [:z1, :z3, :z2])])
    @test keys(state_layout(shuffled)) == (:seed, :z1, :z2, :z3)
end
