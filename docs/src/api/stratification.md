# Stratification & Coarsening

Stratification creates structured population models over multiple patches or environments by taking Kronecker products of projection nets. Coarsening reverses this operation, collapsing a stratified model back to a simpler one.

```@docs
stratify
coarsen
```

```@example catpd
using CategoricalPopulationDynamics

A_local = [0.7 0.3; 0.2 0.8]
coupling = [0.9 0.1; 0.2 0.8]
A_strat = stratify(A_local, coupling)

fine_domain = ContinuousProjectionDomain(0.0, 1.0, 4)
coarse_domain = ContinuousProjectionDomain(0.0, 1.0, 2)
A_coarse = coarsen(A_strat, fine_domain, coarse_domain)

(
    stratified_size = size(A_strat),
    coarsened_matrix = A_coarse,
)
```
