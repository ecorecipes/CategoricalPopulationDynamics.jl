# Diagnostics

Diagnostic functions measure how well a coarsening-refinement round-trip preserves model structure. The unit and counit errors quantify the deviation from exact adjunction identities.

```@docs
unit_error
counit_error
adjunction_errors
```

```@example catpd
using CategoricalPopulationDynamics

domain = ContinuousProjectionDomain(0.0, 1.0, 4)
kernel(z_new, z) = exp(-(z_new - z)^2)
A = left_kan_extension(kernel, domain)

(
    unit = unit_error(A, domain),
    counit = counit_error(kernel, domain; n_quad=31),
    summary = adjunction_errors(kernel, domain; n_quad=31),
)
```
