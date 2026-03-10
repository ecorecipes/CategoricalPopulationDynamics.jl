"""
Lightweight domain types for CategoricalProjectionModels.

These avoid circular dependencies with IntegralProjectionModels while
providing enough structure for Kan extensions and coarsening.
"""

# ---------------------------------------------------------------------------
# Continuous domain
# ---------------------------------------------------------------------------

"""
    ContinuousProjectionDomain{T<:Real}

Continuous state variable domain discretized via the midpoint rule.
"""
struct ContinuousProjectionDomain{T<:Real}
    lower::T
    upper::T
    n_meshpoints::Int

    function ContinuousProjectionDomain(lower::T, upper::T, n::Int) where {T<:Real}
        lower < upper || throw(ArgumentError("lower must be less than upper"))
        n > 0 || throw(ArgumentError("n_meshpoints must be positive"))
        new{T}(lower, upper, n)
    end
end

function ContinuousProjectionDomain(lower::Real, upper::Real, n::Int)
    T = promote_type(typeof(lower), typeof(upper))
    ContinuousProjectionDomain(T(lower), T(upper), n)
end

"""Width of each bin."""
step_size(d::ContinuousProjectionDomain) = (d.upper - d.lower) / d.n_meshpoints

"""Midpoints of the `n_meshpoints` bins."""
function meshpoints(d::ContinuousProjectionDomain)
    n = d.n_meshpoints
    bounds = range(d.lower, d.upper; length=n + 1)
    return [(bounds[i] + bounds[i + 1]) / 2 for i in 1:n]
end

"""Bin edges spanning `[lower, upper]`."""
function bounds(d::ContinuousProjectionDomain)
    collect(range(d.lower, d.upper; length=d.n_meshpoints + 1))
end

n_meshpoints(d::ContinuousProjectionDomain) = d.n_meshpoints

# ---------------------------------------------------------------------------
# Discrete domain
# ---------------------------------------------------------------------------

"""
    DiscreteProjectionDomain

Discrete state variable with a fixed number of classes.
"""
struct DiscreteProjectionDomain
    n::Int
    labels::Vector{Symbol}

    function DiscreteProjectionDomain(n::Int; labels::Vector{Symbol}=Symbol[])
        n > 0 || throw(ArgumentError("n must be positive"))
        if !isempty(labels)
            length(labels) == n || throw(ArgumentError(
                "length(labels) must equal n"))
        end
        new(n, labels)
    end
end

DiscreteProjectionDomain(labels::Vector{Symbol}) =
    DiscreteProjectionDomain(length(labels); labels=labels)

n_meshpoints(d::DiscreteProjectionDomain) = d.n

# ---------------------------------------------------------------------------
# TransitionSpec
# ---------------------------------------------------------------------------

"""
    TransitionSpec

Associates a transition name with its data (kernel function, matrix, or parameters).
"""
struct TransitionSpec{T}
    name::Symbol
    data::T
end
