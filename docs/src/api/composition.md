# Composition

Compositional model construction assembles complex population models from simpler components. Models are composed via undirected wiring diagrams using the structured cospan machinery provided by Catlab.jl.

```@docs
ProjectionSharer
oapply
compose_transitions
compose_from_uwd
```

```@example catpd
using CategoricalPopulationDynamics
using Catlab.WiringDiagrams
using Catlab.Programs: @relation

domain = ContinuousProjectionDomain(0.0, 1.0, 3)
survival_kernel(z_new, z) = z_new >= z ? 0.6 : 0.0
fecundity_kernel(z_new, z) = 0.2 * (1 + z_new + z)

survival_sharer = ProjectionSharer(survival_kernel, domain)
fecundity_sharer = ProjectionSharer(fecundity_kernel, domain)

uwd = @relation (z, z_new) begin
    survival(z, z_new)
    fecundity(z, z_new)
end

composed = oapply(uwd, Dict(
    :survival => survival_sharer,
    :fecundity => fecundity_sharer,
))
combined = compose_transitions(Dict(
    :survival => survival_sharer.matrix,
    :fecundity => fecundity_sharer.matrix,
))
from_kernels = compose_from_uwd(uwd, Dict(
    :survival => survival_kernel,
    :fecundity => fecundity_kernel,
), domain)

(
    size = size(composed.matrix),
    portmap = composed.portmap,
    agrees = combined ≈ composed.matrix ≈ from_kernels,
)
```
