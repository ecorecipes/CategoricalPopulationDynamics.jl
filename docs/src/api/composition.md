# Composition

Compositional model construction assembles complex population models from simpler components. Models are composed via undirected wiring diagrams using the structured cospan machinery provided by Catlab.jl.

`oapply` on sharers merges states and adds constant matrices. Composition in which each box keeps its own states and its rates depend on the totals of the junctions it shares, as in a community of species competing for space, is described under [Open communities](@ref) on the page on responsive nets.

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

# A sharer built from a kernel exposes one port per mesh point (here 3).
survival_sharer = ProjectionSharer(survival_kernel, domain)
fecundity_sharer = ProjectionSharer(fecundity_kernel, domain)

# For `oapply`, each box needs one port per exposed state; each junction
# identifies one mesh point shared by both processes.
uwd = @relation (z1, z2, z3) begin
    survival(z1, z2, z3)
    fecundity(z1, z2, z3)
end

composed = oapply(uwd, Dict(
    :survival => survival_sharer,
    :fecundity => fecundity_sharer,
))
combined = compose_transitions(Dict(
    :survival => survival_sharer.matrix,
    :fecundity => fecundity_sharer.matrix,
))
# `compose_from_uwd` reads only the box names and sums the kernels, so a
# relation over the kernel's two arguments describes the same composition.
kernel_uwd = @relation (z, z_new) begin
    survival(z, z_new)
    fecundity(z, z_new)
end
from_kernels = compose_from_uwd(kernel_uwd, Dict(
    :survival => survival_kernel,
    :fecundity => fecundity_kernel,
), domain)

(
    size = size(composed.matrix),
    portmap = composed.portmap,
    agrees = combined ≈ composed.matrix ≈ from_kernels,
)
```
