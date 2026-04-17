"""
ACSet schemas for compositional projection models.

Follows the AlgebraicPetri pattern: a `ProjectionNet` has States (population
variables) and Transitions (demographic processes) connected by source/target
arcs. Composition is **additive** (kernel/matrix sum), not multiplicative.
"""

# ---------------------------------------------------------------------------
# Schema declarations
# ---------------------------------------------------------------------------

@present SchProjectionNet(FreeSchema) begin
    S::Ob
    T::Ob
    Src::Ob
    Tgt::Ob
    src_t::Hom(Src, T)
    src_s::Hom(Src, S)
    tgt_t::Hom(Tgt, T)
    tgt_s::Hom(Tgt, S)
end

@present SchLabelledProjectionNet <: SchProjectionNet begin
    Name::AttrType
    sname::Attr(S, Name)
    tname::Attr(T, Name)
end

# ---------------------------------------------------------------------------
# ACSet types
# ---------------------------------------------------------------------------

@abstract_acset_type AbstractProjectionNet

@acset_type ProjectionNet(SchProjectionNet,
    index=[:src_t, :src_s, :tgt_t, :tgt_s]) <: AbstractProjectionNet

@acset_type LabelledProjectionNetUntyped(SchLabelledProjectionNet,
    index=[:src_t, :src_s, :tgt_t, :tgt_s]) <: AbstractProjectionNet

const LabelledProjectionNet = LabelledProjectionNetUntyped{Symbol}

# ---------------------------------------------------------------------------
# Open types (structured cospans for composition)
# ---------------------------------------------------------------------------

const OpenProjectionNetOb, OpenProjectionNet = OpenCSetTypes(ProjectionNet, :S)

const OpenLabelledProjectionNetObUntyped, OpenLabelledProjectionNetUntyped =
    OpenACSetTypes(LabelledProjectionNetUntyped, :S)
const OpenLabelledProjectionNetOb = OpenLabelledProjectionNetObUntyped{Symbol}
const OpenLabelledProjectionNet = OpenLabelledProjectionNetUntyped{Symbol}

# ---------------------------------------------------------------------------
# Convenience constructors
# ---------------------------------------------------------------------------

"""
    Open(pn::ProjectionNet, legs...)

Wrap a `ProjectionNet` as an open structured cospan exposing the given state legs.
"""
function Open(pn::ProjectionNet, legs...)
    OpenProjectionNet(pn, map(l -> FinFunction(l, nparts(pn, :S)), legs)...)
end

function Open(pn::LabelledProjectionNet, legs...)
    OpenLabelledProjectionNet(pn,
        map(l -> FinFunction(l, nparts(pn, :S)), legs)...)
end

"""
    LabelledProjectionNet(states, transitions...)

Convenience constructor for a labelled projection net.

# Example
```julia
LabelledProjectionNet([:size],
    :survival_growth => (:size => :size),
    :fecundity => (:size => :size))
```
"""
function LabelledProjectionNet(states::Vector{Symbol},
        transitions::Pair{Symbol, Pair{Symbol, Symbol}}...)
    pn = LabelledProjectionNet()
    state_ids = Dict{Symbol, Int}()
    for s in states
        sid = add_part!(pn, :S; sname=s)
        state_ids[s] = sid
    end
    for (tname_val, (src_name, tgt_name)) in transitions
        haskey(state_ids, src_name) || error("Unknown state :$src_name")
        haskey(state_ids, tgt_name) || error("Unknown state :$tgt_name")
        tid = add_part!(pn, :T; tname=tname_val)
        add_part!(pn, :Src; src_t=tid, src_s=state_ids[src_name])
        add_part!(pn, :Tgt; tgt_t=tid, tgt_s=state_ids[tgt_name])
    end
    return pn
end

# ---------------------------------------------------------------------------
# Accessors
# ---------------------------------------------------------------------------

"""Number of state variables in the projection net."""
n_states(pn::AbstractProjectionNet) = nparts(pn, :S)

"""Number of transitions (demographic processes) in the projection net."""
n_transitions(pn::AbstractProjectionNet) = nparts(pn, :T)

"""Source state indices for transition `t`."""
function sources(pn::AbstractProjectionNet, t::Int)
    src_rows = incident(pn, t, :src_t)
    return subpart(pn, src_rows, :src_s)
end

"""Target state indices for transition `t`."""
function targets(pn::AbstractProjectionNet, t::Int)
    tgt_rows = incident(pn, t, :tgt_t)
    return subpart(pn, tgt_rows, :tgt_s)
end

"""State name for state index `s`."""
sname(pn::LabelledProjectionNet, s::Int) = subpart(pn, s, :sname)

"""Transition name for transition index `t`."""
tname(pn::LabelledProjectionNet, t::Int) = subpart(pn, t, :tname)

"""All state names."""
sname(pn::LabelledProjectionNet) = subpart(pn, :sname)

"""All transition names."""
tname(pn::LabelledProjectionNet) = subpart(pn, :tname)
