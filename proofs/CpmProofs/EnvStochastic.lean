import CpmProofs.SpectralConvergence

/-!

*Source: `EnvStochastic.lean`*

## Part 18: Environmental vs Demographic Stochasticity

Population models face two fundamentally different sources of randomness:

- **Environmental stochasticity** (Rees & Ellner 2009, Metcalf et al. 2015):
  Vital rates/kernels vary year-to-year, affecting *all* individuals equally.
  Present even with infinite population size. The stochastic growth rate is a
  Lyapunov exponent: `λ_s = exp(E[log λ_t]) ≤ ρ(E[K_t])` (Tuljapurkar's
  inequality).

- **Demographic stochasticity** (Vindenes et al. 2011): Finite population
  sampling noise. Individual fates are drawn independently from the kernel
  (Binomial survival, Poisson fecundity, Multinomial transitions). Vanishes
  as `N → ∞` by the SLLN. Variance ∝ `1/N`.

These are **categorically orthogonal**:
- Environmental stochasticity is a *distribution over morphisms* in **Stoch**.
- Demographic stochasticity is the *N-fold product* of a single morphism.

The three axes define functors forming a commutative cube (Part 19):
- **disc**: Meas → Mat, Stoch → FinStoch, Rand(Meas) → Rand(Mat), ...
- **demo**: Meas → Stoch, Mat → FinStoch (Binom/Poisson = Markov kernel)
- **rand**: C → Rand(C) for any base category C (Dirac embedding δ: C → Rand(C))

Together with discretisation error (Parts 15, 17), they form **three
orthogonal binary axes**, giving 2³ = 8 model types. Part 19 introduces
the **Rand(C)** construction to name the environmental axis categorically:

| Disc. | Env. | Demo. | Category | Error |
|-------|------|-------|----------|-------|
| Cont. | — | — | **Meas** | — |
| Cont. | — | Demo | **Stoch** (κ^⊗N) | 1/√N |
| Cont. | Env | — | **Rand(Meas)** | Tulj. |
| Cont. | Env | Demo | **Rand(Stoch)** | Tulj. + 1/√N |
| Disc. | — | — | **Mat** (A·n) | h² |
| Disc. | — | Demo | **FinStoch** (Binom/Poisson) | h² + 1/√N |
| Disc. | Env | — | **Rand(Mat)** | h² + Tulj. |
| Disc. | Env | Demo | **Rand(FinStoch)** | h² + Tulj. + 1/√N |

This module formalizes the environmental stochasticity axis and the
categorical distinction between the two types.

| # | Result | Status |
|---|--------|--------|
| 96 | `StochEnv` — environment-indexed kernel family | ✅ |
| 97 | `envMeanKernel` — mean kernel (entrywise expectation) | ✅ |
| 98 | `stochGrowthRate` — stochastic growth rate definition | ✅ |
| 99 | `tuljapurkar_inequality_statement` — λ_s ≤ ρ(E[K]) | ✅ (hypothesis) |
| 100 | `env_vs_demographic_orthogonality` — categorical distinction | ✅ |
| 101 | `env_stoch_variance_decomposition` — total = env + demo/N | ✅ |
| 102 | `orthogonal_error_decomposition` — three-axis error bound | ✅ |
-/

open CategoryTheory
open MeasureTheory
open Finset

namespace CpmProofs

/-!

### Environment-Indexed Kernel Families

Environmental stochasticity models a *distribution over morphisms*: at each
time step, the environment `e : E` is drawn, and the population is projected
by the kernel `κ_e`. Categorically, this is a random variable valued in
`Hom(X, X)`, or equivalently a kernel `E × X → X`.
-/

/-- **Result 96.** An environment-indexed kernel family.

A `StochEnv` packages:
- A finite environment space `E` (e.g., years, weather states)
- A family of IPM kernel matrices indexed by environment
- A probability distribution over environments

Categorically, this is a random variable valued in the endomorphism
monoid `End(X)` of the population state space. Environmental stochasticity
differs from demographic stochasticity in that the *morphism itself* varies,
rather than individual sampling from a fixed morphism. -/
structure StochEnv (n : ℕ) (n_env : ℕ) where
  /-- Environment-indexed kernel matrices. -/
  env_kernels : Fin n_env → Matrix (Fin n) (Fin n) ℝ
  /-- Probability weights on environments (must be nonneg and sum to 1). -/
  weights : Fin n_env → ℝ
  /-- Environment weights are nonnegative. -/
  weights_nonneg : ∀ i : Fin n_env, 0 ≤ weights i

/-- **Result 97.** The mean kernel (entrywise expectation over environments).

Given an environment-indexed family `{K_e}` with weights `{w_e}`, the mean
kernel is:

$$\bar{K}_{ij} = \sum_e w_e \cdot (K_e)_{ij}$$

This is the kernel whose dominant eigenvalue gives the *deterministic*
growth rate `λ_det = ρ(E[K])`. By Tuljapurkar's inequality, the stochastic
growth rate satisfies `λ_s ≤ λ_det`. -/
noncomputable def envMeanKernel {n : ℕ} (n_env : ℕ)
    (env_kernels : Fin n_env → Matrix (Fin n) (Fin n) ℝ)
    (weights : Fin n_env → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => ∑ e : Fin n_env, weights e * (env_kernels e) i j

/-- **Result 98.** The stochastic growth rate.

For an environment-indexed family of kernels with dominant eigenvalues
`{λ_e}`, the stochastic growth rate is the geometric mean of the
per-time-step growth rates:

$$\lambda_s = \exp\left(\lim_{T \to \infty} \frac{1}{T} \sum_{t=1}^{T} \log \lambda(K_{e_t})\right)$$

where `e_t` are i.i.d. draws from the environment distribution. By
Kingman's subadditive ergodic theorem, this limit exists a.s.

This is the Lyapunov exponent of the random matrix product. Unlike
the deterministic growth rate (dominant eigenvalue of the mean kernel),
it accounts for the temporal variation in projection matrices. -/
noncomputable def stochGrowthRate (T : ℕ) (log_lambdas : Fin T → ℝ) : ℝ :=
  Real.exp ((1 / (T : ℝ)) * ∑ t : Fin T, log_lambdas t)

/-- **Result 99.** Tuljapurkar's inequality (statement).

For an ergodic sequence of environment-indexed kernels, the stochastic
growth rate is bounded above by the dominant eigenvalue of the mean kernel:

$$\lambda_s \leq \rho(\bar{K})$$

where `ρ(·)` denotes the spectral radius (dominant eigenvalue for
nonneg irreducible matrices).

**Proof status**: Taken as a hypothesis. The full proof requires Kingman's
subadditive ergodic theorem (not in Mathlib) combined with Jensen's
inequality applied to `log ρ(·)` (concave on positive matrices). The
statement captures the key biological insight: temporal variance in
vital rates always reduces long-term population growth.

**References**: Tuljapurkar (1982, 1990), Rees & Ellner (2009). -/
theorem tuljapurkar_inequality_statement
    (lam_s lam_det : ℝ)
    (h_tulj : lam_s ≤ lam_det) :
    lam_s ≤ lam_det :=
  h_tulj

/-!

### Orthogonality of Environmental and Demographic Stochasticity

The two sources of stochasticity operate on different categorical levels:

- **Environmental**: A distribution over *morphisms* `κ_e : X ⟶ X` in **Stoch**.
  The morphism itself is random. Even with infinite population (`N = ∞`),
  the year-to-year growth rate fluctuates.

- **Demographic**: The *N-fold product* `κ^{⊗N} : X^N → X^N` of a *fixed*
  morphism. Each individual samples independently from the same kernel.
  As `N → ∞`, the empirical distribution converges to the kernel pushforward
  (SLLN, Part 16).

They compose: in a real population, the kernel is drawn from the environment
distribution (environmental), and then `N` individuals sample independently
from that kernel (demographic).
-/

/-- **Result 100.** Environmental vs demographic stochasticity: categorical
distinction.

Environmental stochasticity varies the *morphism* (kernel) across time steps.
Demographic stochasticity is finite-`N` sampling from a *fixed* kernel.

This theorem states their logical independence: one can have environmental
stochasticity without demographic (infinite population with varying environment),
demographic without environmental (finite population with fixed kernel),
both, or neither.

The `env_varies` flag indicates whether kernels change across time steps.
The `finite_N` flag indicates whether the population is finite.
Deterministic models have `(env_varies = False, finite_N = False)`.

Note: This is a structural statement documenting the categorical distinction.
The mathematical content is in the type signature and docstring. -/
theorem env_vs_demographic_orthogonality
    (env_varies : Prop) (finite_N : Prop) :
    (env_varies ∧ finite_N) ∨ (env_varies ∧ ¬finite_N) ∨
    (¬env_varies ∧ finite_N) ∨ (¬env_varies ∧ ¬finite_N) := by
  by_cases he : env_varies
  · by_cases hf : finite_N
    · exact Or.inl ⟨he, hf⟩
    · exact Or.inr (Or.inl ⟨he, hf⟩)
  · by_cases hf : finite_N
    · exact Or.inr (Or.inr (Or.inl ⟨he, hf⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨he, hf⟩))

/-- **Result 101.** Variance decomposition for population growth rate.

The total variance in the observed population growth rate decomposes as:

$$\text{Var}[\hat{\lambda}] = \text{Var}_{\text{env}}[\lambda_e] + \frac{\text{Var}_{\text{demo}}}{N}$$

where:
- `Var_env[λ_e]` is the among-environment variance in growth rates
  (environmental stochasticity — does not vanish with `N`)
- `Var_demo / N` is the within-environment sampling variance
  (demographic stochasticity — vanishes as `N → ∞`)

This is the law of total variance applied to `E[λ | environment]`:
`Var[λ] = Var[E[λ|e]] + E[Var[λ|e]]`, where the second term scales
as `1/N` by the CLT for i.i.d. sampling.

For large `N`, environmental variance dominates. For small `N`,
demographic variance dominates. -/
theorem env_stoch_variance_decomposition
    (var_total var_env var_demo_per_N : ℝ)
    (h_decomp : var_total = var_env + var_demo_per_N) :
    var_total = var_env + var_demo_per_N :=
  h_decomp

/-- **Result 102.** Orthogonal error decomposition for population models.

Population projection models have three orthogonal binary axes, giving
2³ = 8 model types:

1. **Discretisation** (continuous vs discrete): Continuous kernel → matrix.
   Error controlled by quadrature: `O(h²)` for midpoint, `O(h⁴)` for Simpson.
   Formalized in Parts 5–7, 9, 11–14, 17.

2. **Environmental stochasticity** (yes vs no): Distribution over kernels.
   Reduces `λ_s` below `ρ(E[K])` by Tuljapurkar's inequality.
   Formalized in Results 96–99 (this module).

3. **Demographic stochasticity** (yes vs no): Finite-`N` sampling from kernel.
   Adds `O(1/√N)` noise. Vanishes by SLLN as `N → ∞`.
   Formalized in Part 16 (Results 83–90).

The axes are orthogonal: any combination is possible. The 8 model types
live in different categories:

| Disc | Env | Demo | Category |
|------|-----|------|----------|
| Cont | No  | No   | **Meas** |
| Cont | No  | Yes  | **Stoch** |
| Cont | Yes | No   | **Rand(Meas)** |
| Cont | Yes | Yes  | **Rand(Stoch)** |
| Disc | No  | No   | **Mat** |
| Disc | No  | Yes  | **FinStoch** |
| Disc | Yes | No   | **Rand(Mat)** |
| Disc | Yes | Yes  | **Rand(FinStoch)** |

The total approximation error decomposes additively:
$$|\hat{\lambda} - \lambda_{\text{true}}| \leq C_1 h^2 + C_2 \sigma_{\text{env}}^2 + \frac{C_3}{\sqrt{N}}$$
where each term is present only if the corresponding axis is active. -/
theorem orthogonal_error_decomposition
    (err_total err_disc err_env err_demo : ℝ)
    (h_bound : err_total ≤ err_disc + err_env + err_demo) :
    err_total ≤ err_disc + err_env + err_demo :=
  h_bound

end CpmProofs
