# Open communities composed along undirected wiring diagrams (ported from the composition
# tests of MatrixCommunityModels.jl, with `advance` in place of its `project`).

const OC_K = 1000.0
oc_crowding(ctx) = max(0.0, 1 - ctx.pool.space / OC_K)

function oc_grass(; f = 6.0)
    life = ValuedProjectionNet([:seedling, :adult],
        :establishing => [(:seedling => :adult) => 0.30],
        :persisting => [(:adult => :adult) => 0.50],
        :seeding => [(:adult => :seedling) => f])
    return species(:grass, births(respond(life, :seeding => oc_crowding), :seeding);
                   occupies = [:space => [:seedling => 0.1, :adult => 1.0]])
end

function oc_shrub(; f = 3.0)
    life = ValuedProjectionNet([:seedling, :juvenile, :adult],
        :establishing => [(:seedling => :juvenile) => 0.30],
        :maturing => [(:juvenile => :adult) => 0.50],
        :persisting => [(:adult => :adult) => 0.95],
        :seeding => [(:adult => :seedling) => f])
    return species(:shrub, births(respond(life, :seeding => oc_crowding), :seeding);
                   occupies = [:space => [0.1, 1.0, 4.0]])
end

# `steps` time steps of a community from `n`, as a matrix with one row per time
oc_run(c, n, steps) = permutedims(reduce(hcat, accumulate((m, _) -> advance(c, m, nothing), 1:steps; init = n)))

@testset "open communities" begin
    @testset "species and communities" begin
        grass, shrub = oc_grass(), oc_shrub()
        @test grass isa OpenCommunity && species_names(grass) == [:grass] && pool_names(grass) == [:space]
        @test diagram(grass) === nothing && length(grass) == 2
        com = community(grass, shrub)
        @test species_names(com) == [:grass, :shrub] && pool_names(com) == [:space]
        @test system(com) isa PooledProjectionSystem && component_names(system(com)) == [:grass, :shrub]
        @test diagram(com) isa Catlab.WiringDiagrams.UndirectedWiringDiagram
        @test length(com) == 5 && stage_names(com, :shrub) == [:seedling, :juvenile, :adult]
        @test com[:grass] isa ResponsiveProjectionNet
        @test sprint(show, com) == "OpenCommunity(grass, shrub; pools = space)"
        # the names are Catlab's functions, so loading Catlab alongside does not hide them
        @test compose === Catlab.compose && diagram === Catlab.diagram

        n0 = [50.0, 10.0, 5.0, 0.0, 1.0]
        @test state_vector(com, :shrub => [5.0, 0.0, 1.0], :grass => [50.0, 10.0]) == n0
        @test state_vector(com, [:shrub => [5.0, 0.0, 1.0], :grass => [50.0, 10.0]]) == n0
        v = state_vector(com, n0)
        @test v == n0 && v !== n0
        @test_throws DimensionMismatch state_vector(com, [1.0, 2.0])
        @test species_states(com, n0) == Dict(:grass => [50.0, 10.0], :shrub => [5.0, 0.0, 1.0])
        @test species_states(com, [:grass => [50, 10], :shrub => [5, 0, 1]]) == species_states(com, n0)
        @test state_vector(com, [k => v for (k, v) in species_states(com, n0)]) == n0
        @test pool_totals(com, n0, nothing) == (space = 0.1 * 50 + 10 + 0.1 * 5 + 4.0,)
        @test pool_totals(com, [:grass => [50.0, 10.0], :shrub => [5.0, 0.0, 1.0]], nothing) == pool_totals(com, n0, nothing)
        # one step of the community is one step of its flattened system
        state = Dict(:grass => [50.0, 10.0], :shrub => [5.0, 0.0, 1.0])
        next = advance(system(com), state, nothing)
        @test advance(com, n0, nothing) == vcat(next[:grass], next[:shrub])
        @test advance(com, [:grass => [50.0, 10.0], :shrub => [5.0, 0.0, 1.0]], nothing) == advance(com, n0, nothing)
        @test oc_run(com, n0, 60)[end, :] == vcat(trajectory(system(com), state, fill(nothing, 60)).states[end][:grass],
                                                 trajectory(system(com), state, fill(nothing, 60)).states[end][:shrub])
    end

    @testset "composition along wiring diagrams" begin
        grass, shrub = oc_grass(), oc_shrub()
        com = community(grass, shrub)
        n0 = [50.0, 10.0, 5.0, 0.0, 1.0]
        flat = oc_run(com, n0, 60)

        # an explicit wiring diagram gives the same model
        d = @relation (space,) begin
            grass(space)
            shrub(space)
        end
        @test oc_run(compose(d, [grass, shrub]), n0, 60) == flat
        @test diagram(compose(d, [grass, shrub])) === d

        # composites nest, and grouping does not matter
        herb = species(:herb, respond(ValuedProjectionNet([:plant], :persisting => [(:plant => :plant) => 0.2],
                                                          :seeding => [(:plant => :plant) => 2.0]), :seeding => oc_crowding);
                       occupies = [:space => [0.5]])
        outer = @relation (space,) begin
            a(space)
            b(space)
        end
        n3 = [n0; 20.0]
        three = oc_run(community(grass, shrub, herb), n3, 60)
        @test oc_run(compose(outer, [com, herb]), n3, 60) ≈ three rtol = 1e-13
        @test oc_run(compose(outer, [grass, community(shrub, herb)]), n3, 60) ≈ three rtol = 1e-13

        # a pool that is not exposed is still shared inside, under a private name
        closed = @relation () begin
            grass(space)
            shrub(space)
        end
        cc = compose(closed, [grass, shrub])
        @test isempty(pool_names(cc)) && length(pool_names(cc; internal = true)) == 1
        @test pool_totals(cc, n0, nothing) == NamedTuple()
        @test only(values(pool_totals(cc, n0, nothing; internal = true))) == pool_totals(com, n0, nothing).space
        @test oc_run(cc, n0, 60) == flat

        # a box may call its pool something else: the diagram decides what is shared, and the
        # responses go on reading the pool under the species' own name
        renamed = @relation (ground,) begin
            grass(ground)
            shrub(ground)
        end
        rc = compose(renamed, [grass, shrub])
        @test pool_names(rc) == [:ground] && pool_names(system(rc)) == [:ground]
        @test oc_run(rc, n0, 60) == flat

        # junctions of a diagram without variables are named after the first pool attached
        anonymous = Catlab.WiringDiagrams.UndirectedWiringDiagram(1)
        Catlab.add_junctions!(anonymous, 1)
        for _ in 1:2
            b = Catlab.add_box!(anonymous, 1)
            Catlab.set_junction!(anonymous, Catlab.ports(anonymous, b), [1])
        end
        Catlab.set_junction!(anonymous, [1]; outer = true)
        ac = compose(anonymous, [grass, shrub])
        @test pool_names(ac) == [:space] && oc_run(ac, n0, 60) == flat

        # a species may read a pool without contributing to it
        reader = species(:reader, respond(ValuedProjectionNet([:a], :staying => [(:a => :a) => 1.0]),
                                          :staying => ctx -> 1 / (1 + ctx.pool.space)); reads = [:space])
        rcom = community(grass, reader)
        @test pool_names(rcom) == [:space] && pool_names(reader) == [:space]
        @test advance(rcom, [50.0, 10.0, 1.0], nothing)[3] ≈ 1 / (1 + 15.0)

        # errors
        @test_throws DimensionMismatch compose(d, [grass])
        @test_throws DimensionMismatch compose(d, [grass, herb, shrub])
        @test_throws DimensionMismatch compose((@relation (a, b) begin x(a, b); y(a) end), [grass, shrub])
        @test_throws ArgumentError community(grass, grass)
        @test_throws ArgumentError species(:x, ValuedProjectionNet([:a], :s => [(:a => :a) => 1.0]);
                                           occupies = [:space => 1.0, :space => 2.0])
        @test_throws DimensionMismatch advance(com, [1.0], nothing)
        @test_throws ArgumentError state_vector(com, :grass => [1.0, 1.0])
        @test_throws DimensionMismatch state_vector(com, :grass => [1.0], :shrub => [1.0, 1.0, 1.0])
    end

    @testset "subcommunities" begin
        grass, shrub = oc_grass(), oc_shrub()
        com = community(grass, shrub)
        only_shrub = subcommunity(com, :shrub)
        @test species_names(only_shrub) == [:shrub] && pool_names(only_shrub) == [:space]
        @test oc_run(only_shrub, [5.0, 0.0, 1.0], 30) == oc_run(shrub, [5.0, 0.0, 1.0], 30)
        @test species_names(subcommunity(com, :shrub, :grass)) == [:grass, :shrub]     # community order is kept
        @test_throws ArgumentError subcommunity(com, :herb)
        # a species taken out of a nested composite still reads its (renamed) pool
        inner = compose((@relation () begin
                             grass(space)
                             shrub(space)
                         end), [grass, shrub])
        alone = subcommunity(inner, :grass)
        @test pool_names(alone) == pool_names(inner; internal = true)
        @test oc_run(alone, [50.0, 10.0], 30) == oc_run(grass, [50.0, 10.0], 30)
    end

    @testset "demographic stochasticity" begin
        com = community(oc_grass(), oc_shrub())
        n = [50.0, 10.0, 5.0, 0.0, 1.0]
        a = advance(com, n, nothing; rng = Xoshiro(1))
        @test all(isinteger, a) && all(>=(0), a)
        @test a == advance(com, n, nothing; rng = Xoshiro(1))
        big = [5000.0, 1000.0, 500.0, 100.0, 100.0]
        rng = Xoshiro(3)
        draws = reduce(hcat, [advance(com, big, nothing; rng) for _ in 1:4000])
        @test vec(sum(draws; dims = 2)) ./ 4000 ≈ advance(com, big, nothing) rtol = 0.02
        @test_throws ArgumentError advance(com, [50.5, 10.0, 5.0, 0.0, 1.0], nothing; rng = Xoshiro(1))
        # survival must be a probability: births not marked as such are not
        unmarked = species(:u, ValuedProjectionNet([:a], :s => [(:a => :a) => 1.5]))
        @test_throws ArgumentError advance(unmarked, [3.0], nothing; rng = Xoshiro(1))
        # inflows are Poisson draws
        seeded = species(:s, inflow(ValuedProjectionNet([:a], :s => [(:a => :a) => 0.0]), :a => ctx -> 4.0))
        @test sum(advance(seeded, [0.0], nothing; rng) for _ in 1:4000)[1] / 4000 ≈ 4.0 rtol = 0.05
    end

    @testset "the flattened system lowers" begin
        com = community(oc_grass(), oc_shrub())
        n0 = [50.0, 10.0, 5.0, 0.0, 1.0]
        start = Dict(:grass => n0[1:2], :shrub => n0[3:5])
        sol = MatrixProjectionModels.solve(lower(system(com), StateDependentMPMTarget(start, (0, 20); p = nothing)),
                                           MatrixProjectionModels.DirectIteration())
        @test vcat(sol.u[21][:grass], sol.u[21][:shrub]) == oc_run(com, n0, 20)[end, :]
    end
end
