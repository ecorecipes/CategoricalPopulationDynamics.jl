"""
Projection-system specifications for stateful lowering targets.

`ProjectionSystemNet` bundles multiple local projection-net specifications into
one named system. Each component should support `stage_names` and `to_matrix`
methods (for example `ValuedProjectionNet` and `NestableVPN`).
"""

struct ProjectionSystemNet{C}
    components::Dict{Symbol, C}
    order::Vector{Symbol}
end

function ProjectionSystemNet(pairs::Pair{Symbol}...)
    isempty(pairs) && throw(ArgumentError("ProjectionSystemNet must have at least one component"))

    order = Symbol[]
    specs = Any[]
    for (name, spec) in pairs
        name in order && throw(ArgumentError("duplicate component name: $name"))
        push!(order, name)
        push!(specs, spec)
    end

    component_type = length(specs) == 1 ?
        typeof(specs[1]) :
        foldl(typejoin, map(typeof, specs)[2:end]; init = typeof(specs[1]))

    components = Dict{Symbol, component_type}()
    for (name, spec) in pairs
        components[name] = spec
    end

    return ProjectionSystemNet{component_type}(components, copy(order))
end

Base.getindex(sys::ProjectionSystemNet, name::Symbol) = sys.components[name]
Base.haskey(sys::ProjectionSystemNet, name::Symbol) = haskey(sys.components, name)
Base.keys(sys::ProjectionSystemNet) = sys.order
Base.length(sys::ProjectionSystemNet) = length(sys.order)
Base.pairs(sys::ProjectionSystemNet) = ((name, sys.components[name]) for name in sys.order)

component_names(sys::ProjectionSystemNet) = sys.order

function Base.show(io::IO, sys::ProjectionSystemNet)
    print(io, "ProjectionSystemNet($(length(sys)) components: $(join(sys.order, ", ")))")
end
