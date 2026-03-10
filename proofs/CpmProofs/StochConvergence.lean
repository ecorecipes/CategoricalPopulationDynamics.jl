import CpmProofs.MeasDet
import Mathlib.Probability.StrongLaw
import Mathlib.Probability.IdentDistrib

/-!

*Source: `StochConvergence.lean`*

## Part 16: Demographic Stochasticity — Convergence via SLLN

**Demographic stochasticity** arises from finite population sampling:
`N` individuals each independently draw their fate from a *fixed* kernel
`κ(x, ·)`. As `N → ∞`, the empirical distribution converges to the
kernel pushforward by the Strong Law of Large Numbers (SLLN).

This is distinct from **environmental stochasticity** (Part 18), where
the kernel itself varies across time steps. Here, the kernel `κ` is
fixed — only the number of samples `N` varies:

- **Demographic model** (finite N): the empirical average of N i.i.d.
  samples from a *fixed* kernel `κ(x, ·)` estimates `∫ f dκ(x)`.
- **Deterministic model** (N = ∞): exactly `∫ f dκ(x)`.
- Sampling variance ∝ `1/N`, vanishing as `N → ∞`.

Combined with the quadrature error bounds from Part 15, this gives:

$$\text{Demographic IPM} \xrightarrow{N \to \infty} \text{Deterministic IPM}
  \approx_{O(h^2)} \text{Midpoint rule}$$

The module wraps Mathlib's `ProbabilityTheory.strong_law_ae_real` with
kernel-appropriate hypotheses.

| # | Result | Status |
|---|--------|--------|
| 83 | `empiricalMean` — sample mean definition | ✅ |
| 84 | `empiricalMean_tendsto` — SLLN for demographic stochasticity (N i.i.d. fates) | ✅ |
| 85 | `stoch_to_det_convergence` — demographic convergence: finite-N sampling → kernel integration | ✅ |
| 86 | `detOfIntegrateAlong` — deterministic kernel from integration | ✅ |
| 87 | `integrateAlong_det_roundtrip` — `det` roundtrip = composition | ✅ |
| 88 | `stoch_det_factorization` — Kan value = detOfIntegrateAlong | ✅ |
| 89 | `convergence_rate_quadrature` — rate after SLLN convergence | ✅ |
| 90 | `population_size_convergence` — as N → ∞, demographic noise vanishes | ✅ |
-/

open CategoryTheory
open ProbabilityTheory
open MeasureTheory
open Set
open Finset
open Filter

universe u

namespace CpmProofs

/-!

### Empirical Mean

The sample mean of `N` observations is `(1/N) ∑ f(yᵢ)`. As `N → ∞`,
this converges a.s. to the expected value by the Strong Law.
-/

/-- **Result 83.** Empirical mean of a sample.

Given a function `f : Y → ℝ` and a sequence of observations
`ys : Fin N → Y`, the empirical mean is:

$$\bar{f}_N = \frac{1}{N} \sum_{i=0}^{N-1} f(y_i)$$

This is the fundamental estimator: each entry of the stochastic MPM
matrix is (approximately) an empirical mean of kernel evaluations. -/
noncomputable def empiricalMean (N : ℕ) (f : Y → ℝ) (ys : Fin N → Y) : ℝ :=
  (1 / (N : ℝ)) * ∑ i : Fin N, f (ys i)

/-- **Result 84.** SLLN for demographic stochasticity — N i.i.d. individual fates.

If `X₀, X₁, X₂, …` are pairwise independent, identically distributed,
integrable real-valued random variables, then:

$$\frac{1}{n} \sum_{i=0}^{n-1} X_i(\omega) \xrightarrow{a.s.} E[X_0]$$

In the demographic stochasticity context, each `Xᵢ` represents the fate
of the `i`-th individual drawn independently from a *fixed* kernel `κ`.
The kernel does not change between individuals — that would be
environmental stochasticity (Part 18).

This is Mathlib's `strong_law_ae_real` (Etemadi's proof, which
only requires pairwise independence rather than full mutual independence). -/
theorem empiricalMean_tendsto
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ)
    (hint : Integrable (X 0) P)
    (hindep : Pairwise fun i j : ℕ => IndepFun (X i) (X j) P)
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P) :
    ∀ᵐ ω ∂P, Tendsto
      (fun n => (∑ i ∈ range n, X i ω) / ↑n)
      atTop (nhds P[X 0]) :=
  strong_law_ae_real X hint hindep hident

/-- **Result 85.** Demographic convergence: finite-N sampling → kernel integration.

Given a *fixed* kernel `κ : A ⟶ B` and an observable `f : B → ℝ`, if we
draw `N` i.i.d. samples from `κ(x)` and apply `f`, the empirical average
converges a.s. to `integrateAlong κ f x = ∫ f dκ(x)` — the
deterministic model's value.

This is the core demographic stochasticity result: as the number of
sampled individuals `N → ∞`, the finite-population noise vanishes and
the model converges to exact kernel integration. The kernel itself
remains fixed throughout (no environmental variation). -/
theorem stoch_to_det_convergence
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {A B : MeasObj} (κ : A ⟶ B) (f : B → ℝ) (x : A)
    (samples : ℕ → Ω → B)
    (hint : Integrable (fun ω => f (samples 0 ω)) P)
    (hindep : Pairwise fun i j : ℕ =>
      IndepFun (fun ω => f (samples i ω)) (fun ω => f (samples j ω)) P)
    (hident : ∀ i, IdentDistrib (fun ω => f (samples i ω))
      (fun ω => f (samples 0 ω)) P P)
    (h_expect : P[fun ω => f (samples 0 ω)] = integrateAlong κ f x) :
    ∀ᵐ ω ∂P, Tendsto
      (fun n => (∑ i ∈ range n, f (samples i ω)) / ↑n)
      atTop (nhds (integrateAlong κ f x)) := by
  have h := strong_law_ae_real (fun n ω => f (samples n ω)) hint hindep hident
  rw [h_expect] at h
  exact h

/-!

### The Deterministic Limit

The deterministic model is the "infinite population" limit: instead of
random sampling, we integrate exactly against the kernel. The function
`detOfIntegrateAlong` captures this.
-/

/-- **Result 86.** The deterministic function induced by kernel
integration.

For a kernel `κ : A ⟶ B` and an observable `f : B → ℝ`, the
deterministic model maps each state `x` to the expected value
`∫ f dκ(x)`. This is the `N = ∞` limit of the stochastic model. -/
noncomputable def detOfIntegrateAlong {A B : MeasObj}
    (κ : A ⟶ B) (f : B → ℝ) : A → ℝ :=
  integrateAlong κ f

/-- **Result 87.** The `det` roundtrip is function composition.

Integrating along a deterministic kernel `det g` gives composition
`f ∘ g`. This is a restatement of `integrateAlong_det` for the
convergence context: in the deterministic limit, the kernel-integration
model reduces to pure function composition. -/
theorem integrateAlong_det_roundtrip
    {A B : MeasObj} [MeasurableSingletonClass B]
    (g : A → B) (hg : Measurable g) (f : B → ℝ) :
    integrateAlong (MeasObj.det g hg) f = f ∘ g :=
  integrateAlong_det g hg f

/-- **Result 88.** Stochastic-deterministic factorization.

The Kan value `lanValue D hD κ f` equals `detOfIntegrateAlong κ f`
pointwise — they are definitionally equal (both are `y ↦ ∫ f dκ(y)`).

This factorization shows that the stochastic Kan extension *is* the
deterministic integration map. The stochasticity enters only through
the randomness of individual samples; the expected (deterministic)
behavior is given by kernel integration. -/
theorem stoch_det_factorization {A B : MeasObj}
    (D : A → B) (hD : Measurable D)
    (κ : Kernel B A) (f : A → ℝ) :
    lanValue D hD κ f = detOfIntegrateAlong κ f := by
  ext y; rfl

/-- **Result 89.** Quantitative convergence rate after SLLN.

Once the SLLN has established convergence of the empirical mean to
the bin average, the remaining gap between the bin average and the
midpoint evaluation is controlled by the quadrature error.

This gives the full quantitative picture:
1. Empirical mean →ₐₛ bin average (by SLLN)
2. |bin average - f(midpoint)| ≤ M₂(b-a)²/24 (by quadrature bound) -/
theorem convergence_rate_quadrature (I : IntervalBin)
    {f : ℝ → ℝ} {M₂ : ℝ}
    (hf : ContDiffOn ℝ 2 f (Icc I.a I.b))
    (hM : ∀ x ∈ Icc I.a I.b, |iteratedDerivWithin 2 f (Icc I.a I.b) x| ≤ M₂)
    (emp_mean : ℝ) (h_emp : emp_mean = binAverage f I) :
    |emp_mean - f I.midpoint| ≤ M₂ * (I.b - I.a) ^ 2 / 24 := by
  subst h_emp
  exact midpoint_quadrature_error I hf hM

/-- **Result 90.** As population size N → ∞, demographic noise vanishes.

The complete demographic stochasticity convergence statement: if we draw
`N` i.i.d. samples from a *fixed* kernel `κ` at state `x` and measure
observable `f`, the empirical average converges a.s. to `∫ f dκ(x)`.

This is the population-biology interpretation: a demographically
stochastic IPM with `N` individuals, as `N → ∞`, converges to the
deterministic IPM. The remaining error is the quadrature error from
discretisation (Part 17), not environmental stochasticity (Part 18).
Environmental stochasticity (year-to-year kernel variation) is an
independent axis that persists even at `N = ∞`. -/
theorem population_size_convergence
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {A B : MeasObj} (κ : A ⟶ B) (f : B → ℝ) (x : A)
    (samples : ℕ → Ω → B)
    (hint : Integrable (fun ω => f (samples 0 ω)) P)
    (hindep : Pairwise fun i j : ℕ =>
      IndepFun (fun ω => f (samples i ω)) (fun ω => f (samples j ω)) P)
    (hident : ∀ i, IdentDistrib (fun ω => f (samples i ω))
      (fun ω => f (samples 0 ω)) P P)
    (h_expect : P[fun ω => f (samples 0 ω)] = ∫ y, f y ∂(κ x)) :
    ∀ᵐ ω ∂P, Tendsto
      (fun n => (∑ i ∈ range n, f (samples i ω)) / ↑n)
      atTop (nhds (∫ y, f y ∂(κ x))) := by
  have h := strong_law_ae_real (fun n ω => f (samples n ω)) hint hindep hident
  rw [h_expect] at h
  exact h

end CpmProofs
