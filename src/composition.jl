"""
Composition operators for projection models.

- `oapply`: compose ProjectionSharers via UWD (Catlab-dependent)
- `compose_transitions`: Catlab-free additive sum
- `compose_from_uwd`: UWD evaluation with kernel functions
"""

# ---------------------------------------------------------------------------
# oapply: UWD composition of ProjectionSharers
# ---------------------------------------------------------------------------

"""
    oapply(d::AbstractUWD, sharers::Vector{ProjectionSharer{T}})

Compose ProjectionSharers according to an undirected wiring diagram.

For projection models, composition is additive: sub-kernels sharing the
same state variables sum their contributions.

Each box in the UWD corresponds to a sharer; junctions identify shared
state variables. All sharers must have the same `nstates`.
"""
function oapply(d::AbstractUWD, sharers::Vector{ProjectionSharer{T}}) where {T}
    nboxes_d = nparts(d, :Box)
    length(sharers) == nboxes_d || throw(ArgumentError(
        "Expected $nboxes_d sharers, got $(length(sharers))"))

    n = sharers[1].nstates
    all(s -> s.nstates == n, sharers) || throw(ArgumentError(
        "All sharers must have the same nstates"))

    K = zeros(T, n, n)
    for s in sharers
        K .+= s.matrix
    end

    n_outer = nparts(d, :OuterPort)
    portmap = if n_outer > 0
        outer_junctions = subpart(d, :outer_junction)
        clamp.(outer_junctions, 1, n)
    else
        collect(1:n)
    end

    return ProjectionSharer{T}(length(portmap), n, K, portmap)
end

"""
    oapply(d::AbstractUWD, sharer::ProjectionSharer)

Apply a single sharer replicated across all boxes.
"""
function oapply(d::AbstractUWD, sharer::ProjectionSharer{T}) where {T}
    n = nparts(d, :Box)
    oapply(d, fill(sharer, n))
end

"""
    oapply(d::AbstractUWD, sharers::AbstractDict{Symbol, ProjectionSharer{T}})

Look up sharers by box name in the UWD.
"""
function oapply(d::AbstractUWD,
        sharers::AbstractDict{Symbol, ProjectionSharer{T}}) where {T}
    names = Symbol.(subpart(d, :name))
    ordered = [sharers[nm] for nm in names]
    return oapply(d, ordered)
end

# ---------------------------------------------------------------------------
# compose_transitions: Catlab-free additive sum
# ---------------------------------------------------------------------------

"""
    compose_transitions(sub_matrices)

Additively compose sub-matrices (Dict, NamedTuple, or iterable of pairs).
All matrices must be the same size.
"""
function compose_transitions(sub_matrices)
    K = nothing
    for (_, A) in pairs(sub_matrices)
        if K === nothing
            K = zeros(eltype(A), size(A))
        end
        K .+= A
    end
    K === nothing && error("No sub-matrices provided")
    return K
end

# ---------------------------------------------------------------------------
# compose_from_uwd: UWD evaluation with kernel functions
# ---------------------------------------------------------------------------

"""
    compose_from_uwd(uwd, sub_kernels::Dict, domain::ContinuousProjectionDomain)

Evaluate a UWD with concrete kernel functions. Each box is looked up by name
in `sub_kernels`; composition sums all sub-kernel contributions.
"""
function compose_from_uwd(uwd, sub_kernels::Dict,
        domain::ContinuousProjectionDomain)
    z = meshpoints(domain)
    h = step_size(domain)
    m = length(z)
    K = zeros(m, m)

    n_boxes = nparts(uwd, :Box)
    for b in 1:n_boxes
        box_name = Symbol(subpart(uwd, b, :name))
        haskey(sub_kernels, box_name) || error(
            "No sub-kernel for UWD box :$box_name. " *
            "Available: $(collect(keys(sub_kernels)))")
        kfn = sub_kernels[box_name]
        @inbounds for j in 1:m
            for i in 1:m
                K[i, j] += h * kfn(z[i], z[j])
            end
        end
    end
    return K
end
