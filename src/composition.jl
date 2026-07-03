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
state variables. `ProjectionSharer.portmap` determines which local state each
box port exposes, and states attached to the same junction are quotient-merged
in the composed result.
"""
function _find_root!(parent::Vector{Int}, i::Int)
    while parent[i] != i
        parent[i] = parent[parent[i]]
        i = parent[i]
    end
    return i
end

function _union_roots!(parent::Vector{Int}, i::Int, j::Int)
    ri = _find_root!(parent, i)
    rj = _find_root!(parent, j)
    ri == rj && return ri
    if ri < rj
        parent[rj] = ri
        return ri
    else
        parent[ri] = rj
        return rj
    end
end

function oapply(d::AbstractUWD, sharers::Vector{ProjectionSharer{T}}) where {T}
    nboxes_d = nparts(d, :Box)
    length(sharers) == nboxes_d || throw(ArgumentError(
        "Expected $nboxes_d sharers, got $(length(sharers))"))

    offsets = Vector{Int}(undef, length(sharers))
    total_states = 0
    for (b, s) in enumerate(sharers)
        offsets[b] = total_states
        total_states += s.nstates
    end

    parent = collect(1:total_states)
    junction_anchor = Dict{Int, Int}()

    for (b, s) in enumerate(sharers)
        box_ports = ports(d, b)
        length(box_ports) == s.nports || throw(DimensionMismatch(
            "Box $b has $(length(box_ports)) port(s), but sharer exposes $(s.nports)"))
        for (port_idx, local_state) in enumerate(s.portmap)
            port = box_ports[port_idx]
            junction_id = subpart(d, port, :junction)
            junction_id > 0 || throw(ArgumentError(
                "Box $b port $port_idx is not connected to any junction"))
            global_state = offsets[b] + local_state
            if haskey(junction_anchor, junction_id)
                _union_roots!(parent, junction_anchor[junction_id], global_state)
            else
                junction_anchor[junction_id] = global_state
            end
        end
    end

    state_index_by_global = Vector{Int}(undef, total_states)
    root_to_state = Dict{Int, Int}()
    next_state = 0
    for global_state in 1:total_states
        root = _find_root!(parent, global_state)
        merged_state = get!(root_to_state, root) do
            next_state += 1
            next_state
        end
        state_index_by_global[global_state] = merged_state
    end

    junction_to_state = Dict{Int, Int}()
    for (junction_id, global_state) in junction_anchor
        junction_to_state[junction_id] = state_index_by_global[global_state]
    end

    for junction_id in subpart(d, :outer_junction)
        junction_id > 0 || throw(ArgumentError(
            "Outer ports must be connected to a junction"))
        if !haskey(junction_to_state, junction_id)
            next_state += 1
            junction_to_state[junction_id] = next_state
        end
    end

    K = zeros(T, next_state, next_state)
    for (b, s) in enumerate(sharers)
        offset = offsets[b]
        for from_state in 1:s.nstates
            merged_from = state_index_by_global[offset + from_state]
            for to_state in 1:s.nstates
                merged_to = state_index_by_global[offset + to_state]
                K[merged_to, merged_from] += s.matrix[to_state, from_state]
            end
        end
    end

    n_outer = nparts(d, :OuterPort)
    portmap = if n_outer > 0
        [junction_to_state[junction_id] for junction_id in subpart(d, :outer_junction)]
    else
        Int[]
    end

    return ProjectionSharer{T}(length(portmap), next_state, K, portmap)
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
