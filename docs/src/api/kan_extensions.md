# Kan Extensions

Left and right Kan extensions provide a principled way to change the resolution of a population model's state space. The left Kan extension coarsens (aggregates) states, while the right Kan extension refines (disaggregates) them. Together they form an adjunction that formally relates IPMs and MPMs.

```@docs
left_kan_extension
right_kan_extension
```

```@example catpd
using CategoricalPopulationDynamics

domain = ContinuousProjectionDomain(0.0, 1.0, 4)
kernel(z_new, z) = z_new + z

A = left_kan_extension(kernel, domain)
K_pw = right_kan_extension(A, domain)
z = meshpoints(domain)

(
    matrix = A,
    reconstructed_entry = K_pw(z[1], z[2]),
)
```
