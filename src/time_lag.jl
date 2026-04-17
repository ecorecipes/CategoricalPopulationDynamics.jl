"""
Time-lagged categorical projection models.

Provides functorial expansion of projection nets with time-delay structure:
states `S → S × {0,...,L}` (L+1 copies), transitions placed at assigned lag
offsets, plus identity shift transitions on the sub-diagonal.
"""

using StructuredPopulationCore: TimeLagStructure, expand_lag_matrix

"""
    lag_expand(pn::LabelledProjectionNet, lag_assignment::Dict{Symbol, Int})

Expand a `LabelledProjectionNet` with time-lag structure.

Each state `s` becomes `L+1` copies `s_lag0, s_lag1, ..., s_lagL`. Each transition
is placed at its assigned lag offset (default 0 = immediate). Identity shift
transitions `shift_s_lag{k}_to_{k+1}` are added on the sub-diagonal.

Returns a new `LabelledProjectionNet` with the expanded state and transition sets.
"""
function lag_expand(pn::LabelledProjectionNet,
        lag_assignment::Dict{Symbol, Int})
    max_lag = maximum(values(lag_assignment); init=0)
    max_lag > 0 || throw(ArgumentError("At least one lag must be > 0"))

    states_orig = sname(pn)
    n_s = length(states_orig)

    # Build expanded state names: s_lag0, s_lag1, ...
    expanded_states = Symbol[]
    for k in 0:max_lag
        for s in states_orig
            push!(expanded_states, Symbol(s, :_lag, k))
        end
    end

    # Build expanded transitions
    transitions = Pair{Symbol, Pair{Symbol, Symbol}}[]

    # Original transitions placed at their lag offset
    n_t = n_transitions(pn)
    for t_idx in 1:n_t
        t_name = tname(pn, t_idx)
        lag_k = get(lag_assignment, t_name, 0)
        src_states = sources(pn, t_idx)
        tgt_states = targets(pn, t_idx)
        for (si, ti) in zip(src_states, tgt_states)
            src_name = sname(pn, si)
            tgt_name = sname(pn, ti)
            # Source from lag_k copy, target to lag_0 copy
            expanded_src = Symbol(src_name, :_lag, lag_k)
            expanded_tgt = Symbol(tgt_name, :_lag, 0)
            expanded_tname = lag_k == 0 ? Symbol(t_name, :_lag0) : Symbol(t_name, :_lag, lag_k)
            push!(transitions, expanded_tname => (expanded_src => expanded_tgt))
        end
    end

    # Identity shift transitions: s_lag{k} → s_lag{k+1} for k = 0, ..., L-1
    for k in 0:(max_lag - 1)
        for s in states_orig
            src = Symbol(s, :_lag, k)
            tgt = Symbol(s, :_lag, k + 1)
            shift_name = Symbol(:shift_, s, :_lag, k, :_to_, k + 1)
            push!(transitions, shift_name => (src => tgt))
        end
    end

    return LabelledProjectionNet(expanded_states, transitions...)
end

"""
    lag_expand(vnet::ValuedProjectionNet, lag_assignment::Dict{Symbol, Int})

Expand a `ValuedProjectionNet` with time-lag structure, preserving transition values.

Transitions are placed at their assigned lag offset, and identity shift transitions
(value = 1.0) are added on the sub-diagonal. The result can be materialized via
`to_matrix` to produce the `(L+1)n × (L+1)n` augmented projection matrix.
"""
function lag_expand(vnet::ValuedProjectionNet{T},
        lag_assignment::Dict{Symbol, Int}) where {T}
    max_lag = maximum(values(lag_assignment); init=0)
    max_lag > 0 || throw(ArgumentError("At least one lag must be > 0"))

    stages = stage_names(vnet)
    n = length(stages)

    # Build expanded stage names
    expanded_stages = Symbol[]
    for k in 0:max_lag
        for s in stages
            push!(expanded_stages, Symbol(s, :_lag, k))
        end
    end

    # Build expanded transitions with values
    expanded_transitions = Pair{Symbol, Vector{Pair{Pair{Symbol,Symbol}, T}}}[]

    for (t_name, entries) in vnet.transition_values
        lag_k = get(lag_assignment, t_name, 0)
        expanded_tname = lag_k == 0 ? Symbol(t_name, :_lag0) : Symbol(t_name, :_lag, lag_k)
        expanded_entries = Pair{Pair{Symbol,Symbol}, T}[]
        for ((from, to), val) in entries
            # Source from lag_k copy, target to lag_0 copy
            expanded_from = Symbol(from, :_lag, lag_k)
            expanded_to = Symbol(to, :_lag, 0)
            push!(expanded_entries, (expanded_from => expanded_to) => val)
        end
        push!(expanded_transitions, expanded_tname => expanded_entries)
    end

    # Identity shift transitions: value = 1.0
    for k in 0:(max_lag - 1)
        for s in stages
            src = Symbol(s, :_lag, k)
            tgt = Symbol(s, :_lag, k + 1)
            shift_name = Symbol(:shift_, s, :_lag, k, :_to_, k + 1)
            push!(expanded_transitions, shift_name => [(src => tgt) => one(T)])
        end
    end

    return ValuedProjectionNet(expanded_stages, expanded_transitions...)
end

"""
    lag_stratify(components::AbstractVector{<:AbstractMatrix},
                 dispersal::AbstractMatrix,
                 lag_structure::TimeLagStructure)

Combined time-lag and spatial stratification.

First builds the `(L+1)m × (L+1)m` lag-augmented matrix from `components`,
then applies spatial stratification with the `dispersal` matrix.

This commutes with the reverse order (stratify first, then lag-expand).
"""
function lag_stratify(components::AbstractVector{<:AbstractMatrix},
        dispersal::AbstractMatrix,
        lag_structure::TimeLagStructure)
    K_lag = expand_lag_matrix(components, lag_structure)
    return stratify(K_lag, dispersal)
end
