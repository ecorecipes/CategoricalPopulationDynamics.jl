"""
Lowering/lifting stubs for converting between categorical specifications
and concrete projection model objects.

Concrete implementations are provided by package extensions
(CategoricalProjectionModelsIPMExt and CategoricalProjectionModelsMPMExt).
"""

# ---------------------------------------------------------------------------
# Abstract target types
# ---------------------------------------------------------------------------

"""Abstract base for lowering targets."""
abstract type AbstractLoweringTarget end

"""
    IPMTarget

Target for lowering a ProjectionNet to an `IPMProblem`.
Requires domain specifications for each state variable.
"""
struct IPMTarget <: AbstractLoweringTarget
    domains::Dict{Symbol, ContinuousProjectionDomain}
end

IPMTarget(pairs::Pair{Symbol}...) = IPMTarget(Dict(pairs...))

"""
    MPMTarget

Target for lowering a ProjectionNet to a `MatrixProjectionModel`.
"""
struct MPMTarget <: AbstractLoweringTarget end

"""
    ProjectionNetTarget

Target for lifting a concrete model back to a `LabelledProjectionNet`.
"""
struct ProjectionNetTarget <: AbstractLoweringTarget end

# ---------------------------------------------------------------------------
# Function stubs (extended by package extensions)
# ---------------------------------------------------------------------------

"""
    lower(net::LabelledProjectionNet, target::AbstractLoweringTarget, transition_data)

Lower a categorical projection net specification to a concrete model object.

- `IPMTarget`: produces an `IPMProblem` (requires IntegralProjectionModels extension)
- `MPMTarget`: produces a `MatrixProjectionModel` (requires MatrixProjectionModels extension)
"""
function lower end

"""
    lift(model, target::ProjectionNetTarget)

Lift a concrete model object back to a `LabelledProjectionNet`.

- From `MatrixProjectionModel`: extracts states and transitions
"""
function lift end
