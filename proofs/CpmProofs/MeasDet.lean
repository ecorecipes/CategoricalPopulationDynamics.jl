import CpmProofs.KanBridge
import CpmProofs.BinExample
import CpmProofs.SimpsonRule

/-!

*Source: `MeasDet.lean`*

## Part 15: Deterministic Kan Extensions in Meas

IPMs and MPMs can be deterministic (infinite population, no randomness)
or stochastic (finite population, sampling noise). The existing
formalization works entirely in **Stoch** (Markov kernels as morphisms).
This module develops the **deterministic** Kan extension in **Meas**
(measurable functions as morphisms), showing:

1. The deterministic Kan extension is simply function composition — no
   integration needed.
2. It is **strictly unique** (not just a.e.), contrasting with the
   stochastic case.
3. The `det` functor preserves Kan values: embedding a deterministic
   extension into **Stoch** via Dirac kernels recovers the stochastic
   Kan extension.
4. The gap between stochastic and deterministic Kan values equals the
   quadrature error.

### Key Insight

The existing `det` functor (`StochCat.lean:184`) embeds measurable
functions as Dirac kernels, and `integrateAlong_det` (`Integration.lean:55`)
already proves integration against a deterministic kernel = function
composition. This module builds on these to define a standalone
deterministic Kan extension that is strictly unique (not a.e.), and
proves it is preserved by `det`.

| # | Result | Status |
|---|--------|--------|
| 73 | `MeasHom` — bundled measurable function type | ✅ |
| 74 | `lanValueDet` — deterministic Kan extension as composition | ✅ |
| 75 | `lanValueDet_eq_comp` — explicit formula | ✅ |
| 76 | `lanValueDet_unique` — strict uniqueness | ✅ |
| 77 | `det_preserves_lanValue` — `det` preserves Kan values | ✅ |
| 78 | `lanValue_det_isStochKanExtension` — det Kan satisfies stoch predicate | ✅ |
| 79 | `midpoint_det_exact` — zero error for deterministic midpoint | ✅ |
| 80 | `stoch_vs_det_lanValue` — gap = quadrature error (midpoint) | ✅ |
| 81 | `stoch_vs_det_simpson` — gap with Simpson quadrature | ✅ |
| 82 | `det_vs_stoch_summary` — summary comparison | ✅ |
-/

open CategoryTheory
open ProbabilityTheory
open MeasureTheory
open Set

universe u

namespace CpmProofs

/-!

### Bundled Measurable Functions

The objects of **Meas** are the same as **Stoch** (`MeasObj`), but the
morphisms are measurable functions rather than Markov kernels. We define
a lightweight `MeasHom` bundling a function with its measurability proof.
-/

/-- **Result 73.** Bundled measurable function — a morphism in **Meas**.

A `MeasHom X Y` pairs a function `X → Y` with a proof that it is
measurable. These are the morphisms of the category **Meas** of
measurable spaces and measurable functions. -/
structure MeasHom (X Y : MeasObj) where
  /-- The underlying function. -/
  toFun : X → Y
  /-- The function is measurable. -/
  measurable : Measurable toFun

instance {X Y : MeasObj} : FunLike (MeasHom X Y) X Y where
  coe := MeasHom.toFun
  coe_injective' f g h := by cases f; cases g; congr

/-- Identity measurable function. -/
def MeasHom.id (X : MeasObj) : MeasHom X X :=
  ⟨_root_.id, measurable_id⟩

/-- Composition of measurable functions. -/
def MeasHom.comp {X Y Z : MeasObj} (g : MeasHom Y Z) (f : MeasHom X Y) : MeasHom X Z :=
  ⟨g.toFun ∘ f.toFun, g.measurable.comp f.measurable⟩

/-!

### Deterministic Kan Extension

For a section `s : Y → X` (e.g., midpoint selection), the deterministic
Kan extension of `f : X → ℝ` is simply `f ∘ s`. No integration needed —
this is the key simplification of the deterministic setting.
-/

/-- **Result 74.** Deterministic Kan extension as function composition.

For a section `s : Y → X` (e.g., a midpoint selector that picks a
representative point in each bin), the deterministic left Kan extension
of `f : X → ℝ` along the coarsening is simply `f ∘ s`. No integration,
no measure theory — just composition.

Compare with `lanValue` (KanBridge.lean), which requires a conditional
kernel κ and produces `y ↦ ∫ f dκ_y`. In the deterministic limit,
the kernel concentrates at a single point, and integration reduces
to evaluation. -/
noncomputable def lanValueDet {X Y : MeasObj}
    (s : Y → X) (_hs : Measurable s) (f : X → ℝ) : Y → ℝ :=
  f ∘ s

/-- **Result 75.** The deterministic Kan extension is function composition.

This is `rfl` — the definition is the theorem. Stated explicitly for
parallel structure with the stochastic case. -/
theorem lanValueDet_eq_comp {X Y : MeasObj}
    (s : Y → X) (hs : Measurable s) (f : X → ℝ) :
    lanValueDet s hs f = f ∘ s :=
  rfl

/-- **Result 76.** Strict uniqueness of the deterministic Kan extension.

If `Lf` and `Lg` both equal `lanValueDet s hs f`, then `Lf = Lg`
**pointwise** — not just a.e. This contrasts sharply with the
stochastic case (`ae_unique` in KanBridge.lean:209), where uniqueness
only holds up to a.e. equality with respect to the pushforward measure.

The deterministic Kan extension is strictly unique because there is no
measure involved — no null sets, no a.e. ambiguity. -/
theorem lanValueDet_unique {X Y : MeasObj}
    (s : Y → X) (hs : Measurable s) (f : X → ℝ)
    {Lf Lg : Y → ℝ}
    (hLf : Lf = lanValueDet s hs f)
    (hLg : Lg = lanValueDet s hs f) :
    Lf = Lg := by
  rw [hLf, hLg]

/-- **Result 77.** The `det` functor preserves Kan values.

Embedding a measurable section `s : Y → X` as a Dirac kernel
`det s hs`, the stochastic Kan value `lanValue` recovers the
deterministic Kan value `lanValueDet`. This is the bridge between
the deterministic and stochastic worlds:

$$\int f\, \mathrm{d}\delta_{s(y)} = f(s(y)) = (\text{lanValueDet}\; s\; f)(y)$$

The proof reduces to `Kernel.integral_deterministic`: integrating
against a Dirac measure evaluates the function at the point. -/
theorem det_preserves_lanValue {X Y : MeasObj} [MeasurableSingletonClass X]
    (D : X → Y) (hD : Measurable D)
    (s : Y → X) (hs : Measurable s) (f : X → ℝ)
    (y : Y) :
    lanValue D hD (MeasObj.det s hs) f y = lanValueDet s hs f y := by
  simp only [lanValue, lanValueDet, Function.comp, MeasObj.det]
  exact Kernel.integral_deterministic hs

/-- **Result 78.** The deterministic Kan extension satisfies the
stochastic Kan extension predicate.

When `s` is a measurable section of `D` with `D ∘ s = id` and
`s ∘ D =ᵐ[μ] id`, the function `lanValueDet s hs f = f ∘ s`
satisfies `IsStochKanExtension`. This formally shows that
deterministic models are a special case of stochastic ones.

The proof bypasses the `IsCondKernelMap` machinery entirely:
1. Rewrite the RHS via `setIntegral_map` (pushforward integral identity).
2. Show `f(x) = f(s(D(x)))` a.e. via the retract condition.

The hypothesis `h_retract : s ∘ D =ᵐ[μ] id` means the measure `μ`
is essentially supported on the image of `s`. Together with
`h_section : D ∘ s = id`, this ensures the Dirac kernel `det s`
is a conditional kernel for `μ` along `D`. -/
theorem lanValue_det_isStochKanExtension
    {X Y : MeasObj} [MeasurableSingletonClass X]
    (D : X → Y) (hD : Measurable D)
    (s : Y → X) (hs : Measurable s)
    (μ : Measure X)
    (f : X → ℝ)
    (hf : Measurable f)
    (_hf_int : Integrable f μ)
    (_h_section : D ∘ s = _root_.id)
    (h_retract : ∀ᵐ x ∂μ, s (D x) = x) :
    IsStochKanExtension D μ (lanValueDet s hs f) f where
  measurable_D := hD
  setIntegral_factorization B hB := by
    -- lanValueDet s hs f = f ∘ s by definition; unfold for setIntegral_map
    unfold lanValueDet
    -- Step 1: Rewrite RHS via pushforward integral identity
    have h1 := setIntegral_map (g := D) (f := f ∘ s) (s := B) (μ := μ)
      hB (Measurable.aestronglyMeasurable (Measurable.comp hf hs))
      hD.aemeasurable
    rw [h1]
    -- Step 2: f(x) = f(s(D(x))) for μ-a.e. x (by h_retract: s(D(x)) = x)
    simp only [Function.comp]
    exact setIntegral_congr_ae (hD hB)
      (h_retract.mono fun x hx _ => congrArg f hx.symm)

/-!

### Deterministic Midpoint Evaluation

In the deterministic setting, evaluating at the midpoint is *exact* —
there is no quadrature error. This provides a clean baseline for
comparison with the stochastic (bin-averaged) setting.
-/

/-- **Result 79.** Zero error for deterministic midpoint evaluation.

The deterministic Kan extension at a single bin, using the midpoint
as the section, simply evaluates `f` at the midpoint — no error at all.
This is `rfl`: `(f ∘ (fun _ => midpoint)) () = f(midpoint)`.

Compare with the stochastic case, where the Kan value is the bin
average `(1/(b-a)) ∫_a^b f`, which differs from `f(midpoint)` by
the quadrature error `O(h²)`. -/
theorem midpoint_det_exact (I : IntervalBin) (f : ℝ → ℝ) :
    lanValueDet (X := ℝObj) (Y := unitObj)
      (fun _ => I.midpoint) measurable_const f ()
    = f I.midpoint :=
  rfl

/-!

### Stochastic vs. Deterministic Comparison

The gap between stochastic and deterministic Kan values is precisely
the quadrature error. This quantifies the fundamental insight:
as the stochastic model approaches the deterministic limit (bin width → 0),
the two agree up to `O(h²)` or `O(h⁴)` depending on the quadrature rule.
-/

/-- **Result 80.** The gap between stochastic and deterministic Kan
values equals the quadrature error (midpoint rule).

The stochastic Kan value (bin average) differs from the deterministic
one (midpoint evaluation) by at most `M₂ · (b-a)² / 24`:

$$\bigl|\text{binAverage}(f, I) - f(\text{midpoint})\bigr|
  \le \frac{M_2\,(b-a)^2}{24}$$

This follows directly from `midpoint_quadrature_error`. The result
quantifies: the stochastic Kan value converges to the deterministic
one at rate `O(h²)` as the bin width `h = b - a` shrinks to zero. -/
theorem stoch_vs_det_lanValue (I : IntervalBin) {f : ℝ → ℝ} {M₂ : ℝ}
    (hf : ContDiffOn ℝ 2 f (Icc I.a I.b))
    (hM : ∀ x ∈ Icc I.a I.b, |iteratedDerivWithin 2 f (Icc I.a I.b) x| ≤ M₂) :
    |binAverage f I - lanValueDet (X := ℝObj) (Y := unitObj)
      (fun _ => I.midpoint) measurable_const f ()|
    ≤ M₂ * (I.b - I.a) ^ 2 / 24 := by
  -- lanValueDet at midpoint = f(midpoint) by rfl
  show |binAverage f I - f I.midpoint| ≤ M₂ * (I.b - I.a) ^ 2 / 24
  exact midpoint_quadrature_error I hf hM

/-- **Result 81.** The gap between bin average and Simpson quadrature.

For `C⁴` functions, Simpson's rule gives `O(h⁴)` approximation:

$$\bigl|\text{binAverage}(f, I) - S(f, I)\bigr|
  \le \frac{M_4\,(b-a)^4}{720}$$

This is a direct application of `simpson_quadrature_error` from
SimpsonRule.lean, restated here for the Meas/Stoch comparison. -/
theorem stoch_vs_det_simpson (I : IntervalBin) {f : ℝ → ℝ} {M₄ : ℝ}
    (hf : ContDiffOn ℝ 4 f (Icc I.a I.b))
    (hM : ∀ x ∈ Icc I.a I.b,
      |iteratedDerivWithin 4 f (Icc I.a I.b) x| ≤ M₄) :
    |binAverage f I - simpsonAverage f I| ≤ M₄ * (I.b - I.a) ^ 4 / 720 :=
  simpson_quadrature_error I hf hM

/-- **Result 82.** Summary comparison: deterministic and stochastic
Kan values agree up to quadrature error.

States the fundamental relationship: for any kernel `κ` that computes
bin averages, the stochastic Kan value `lanValue D hD κ f` and the
deterministic Kan value `lanValueDet s hs f` differ by at most the
midpoint quadrature error `M₂ · (b-a)² / 24`.

This is the key convergence result: as population size N → ∞,
stochastic models approach deterministic ones, and the remaining
gap is controlled by the mesh resolution. -/
theorem det_vs_stoch_summary (I : IntervalBin) {f : ℝ → ℝ} {M₂ : ℝ}
    (hf : ContDiffOn ℝ 2 f (Icc I.a I.b))
    (hM : ∀ x ∈ Icc I.a I.b, |iteratedDerivWithin 2 f (Icc I.a I.b) x| ≤ M₂)
    (κ : Kernel Unit ℝ)
    (hκ : ∀ _u : Unit, (∫ x, f x ∂(κ ())) = binAverage f I) :
    |lanValue (X := ℝObj) (Y := unitObj)
      (fun _x : ℝ => ()) measurable_const κ f ()
    - lanValueDet (X := ℝObj) (Y := unitObj)
      (fun _ => I.midpoint) measurable_const f ()|
    ≤ M₂ * (I.b - I.a) ^ 2 / 24 := by
  rw [lanValue_eq_binAverage f I κ hκ]
  exact stoch_vs_det_lanValue I hf hM

end CpmProofs
