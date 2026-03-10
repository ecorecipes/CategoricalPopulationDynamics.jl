import CpmProofs.KanBridge
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!

*Source: `BinExample.lean`*

## Part 5: Concrete Application — Interval Binning

We now apply the bridge theorem to a concrete setting: **interval binning**
on the real line. This is the core numerical operation underlying Integral
Projection Models (IPMs) in ecology: a continuous kernel `K(z', z)` is
discretised by averaging over bins `[a_i, b_i]`.

### Setup

- **State space**: `ℝ` (e.g., body size of organisms)
- **Coarsening map**: `D : ℝ → Unit` (collapses the interval `[a, b]` to a
  point — the simplest possible binning with a single bin)
- **Conditional kernel**: Normalized Lebesgue measure on `[a, b]`:
  $$\kappa_\star = \frac{1}{b - a}\, \lambda\big|_{[a,b]}$$

### Results

1. **binKernel**: The conditional kernel for a single interval bin is
   `(1/(b-a)) · volume.restrict [a,b]`, constructed as a constant kernel.

2. **binKernel_integral**: Integration against the bin kernel equals the
   **bin average**:
   $$\int f\, \mathrm{d}\kappa_\star = \frac{1}{b-a}\int_a^b f(x)\, \mathrm{d}x$$

3. **lanValue_eq_binAverage**: The Kan extension value at `()` equals the
   bin average (connecting the abstract bridge to the concrete formula).

4. **midpoint_approximates_lanValue**: The **midpoint quadrature** rule
   approximates the Kan value to order `O(h²)`:
   $$\left|(\text{Lan}_D\, f)(\star) - f\!\left(\tfrac{a+b}{2}\right)\right|
     \le \frac{M_2\, (b-a)^2}{24}$$
   where `M₂` bounds the second derivative of `f` on `[a, b]`.

This last result formally justifies the midpoint rule used in IPM
discretisation: the error is controlled by the mesh width squared.
-/

open CategoryTheory
open ProbabilityTheory
open MeasureTheory
open Set

universe u

namespace CpmProofs

/-- The real line as a bundled measurable object. -/
noncomputable def ℝObj : MeasObj := ⟨ℝ, inferInstance⟩

/-- The unit type as a bundled measurable object.

This represents the "trivial" coarsening: collapsing all of ℝ to a
single point. In the context of interval binning, this models a single
bin `[a, b]`. -/
def unitObj : MeasObj := ⟨Unit, inferInstance⟩

/-- A simple interval bin `[a, b]` with `a < b`. -/
structure IntervalBin where
  a : ℝ
  b : ℝ
  hab : a < b

/-- Midpoint of a bin: `(a + b) / 2`. -/
noncomputable def IntervalBin.midpoint (I : IntervalBin) : ℝ :=
  (I.a + I.b) / 2

/-- **Bin average** of a function `f` over an interval `[a, b]`:

$$\text{binAverage}(f, I) = \frac{1}{b - a}\int_a^b f(x)\, \mathrm{d}x$$

This is the fundamental quantity in IPM discretisation: the matrix entry
`A_{ij}` is (up to a factor of `h`) the bin average of the kernel
`K(z_i, ·)` over bin `j`. -/
noncomputable def binAverage (f : ℝ → ℝ) (I : IntervalBin) : ℝ :=
  (1 / (I.b - I.a)) * ∫ x in I.a..I.b, f x

/-!

### The Bin Kernel

From the perspective of Cho–Jacobs [arXiv:1709.00322, §4], the conditional
kernel for the unique map `ℝ → Unit` along the restriction of Lebesgue
measure to `[a, b]` gives the normalized measure `(1/(b-a)) · λ|_{[a,b]}`
on the (unique) fiber. We construct this as a constant kernel.
-/

/-- **The conditional kernel for a single interval bin.**

This is the normalized Lebesgue measure on `[a, b]`:
$$\kappa_\star = \frac{1}{b-a}\, \text{volume.restrict}\ [a,b]$$

Constructed as `Kernel.const Unit (...)`, since the only fiber
(over `() : Unit`) gets the full normalized measure. -/
noncomputable def binKernel (I : IntervalBin) : Kernel Unit ℝ :=
  Kernel.const Unit
    (ENNReal.ofReal (1 / (I.b - I.a)) • volume.restrict (Icc I.a I.b))

/-- **Integration against the bin kernel equals the bin average.**

$$\int f\, \mathrm{d}\kappa_\star = \frac{1}{b-a}\int_a^b f(x)\, \mathrm{d}x$$

This connects the concrete conditional kernel to the abstract bin-average
formula via `integral_smul_measure` and the relationship between set
integrals on `Icc` and interval integrals. -/
theorem binKernel_integral (f : ℝ → ℝ) (I : IntervalBin) :
    (∫ x, f x ∂(binKernel I ())) = binAverage f I := by
  simp only [binKernel, Kernel.const_apply]
  rw [integral_smul_measure]
  -- Goal: ENNReal.toReal (ENNReal.ofReal (1 / (I.b - I.a))) • ∫ x in Icc I.a I.b, f x ∂volume
  --     = (1 / (I.b - I.a)) * ∫ x in I.a..I.b, f x
  have hpos : (0 : ℝ) < I.b - I.a := sub_pos.mpr I.hab
  rw [ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ 1 / (I.b - I.a))]
  rw [smul_eq_mul]
  congr 1
  -- Show: ∫ x in Icc I.a I.b, f x ∂volume = ∫ x in I.a..I.b, f x
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le I.hab.le]

/-!

### The Bin Kernel Is a Conditional Kernel

We show that `binKernel I` satisfies the `IsCondKernelMap` interface for
the trivial coarsening `D : ℝ → Unit` with respect to `volume.restrict [a,b]`.
This closes **Gap 3**: the bin example is connected to the bridge theorem
via a genuine `IsCondKernelMap` instance, not just an ad hoc integral identity.

Since the target space is `Unit`, the proof is elementary:
- **Fiber support**: `D x = ()` is trivially true for all `x`.
- **Set-integral disintegration**: For `B ⊆ Unit`, case-split on `() ∈ B`:
  - `() ∉ B`: both sides are zero (preimage is empty, integral over empty set).
  - `() ∈ B`: the preimage is all of `ℝ`, and the measure arithmetic
    cancels: `(b-a) · (1/(b-a)) · ∫ = ∫`.
-/

/-- **The bin kernel is a conditional kernel for the trivial coarsening.**

The normalized Lebesgue measure on `[a, b]` satisfies the `IsCondKernelMap`
interface for `D = fun _ => () : ℝ → Unit` and `μ = volume.restrict [a,b]`.

This is the concrete instance that connects the bin example to the abstract
bridge theorem. Combined with `lanValue_isStochKanExtension`, it shows that
the bin average is a genuine stochastic Kan extension. -/
theorem binKernel_isCondKernelMap (I : IntervalBin) :
    IsCondKernelMap (fun (_ : ℝ) => ()) (volume.restrict (Icc I.a I.b)) (binKernel I) where
  measurable_D := measurable_const
  ae_mem_fiber := by
    -- D x = () is trivially true for all x : ℝ and y : Unit
    apply Filter.Eventually.of_forall
    intro y
    apply Filter.Eventually.of_forall
    intro x
    exact Subsingleton.elim _ _
  setIntegral_disintegration := by
    intro f _hf_meas _hf_int B hB
    -- Y = Unit: case split on whether () ∈ B.
    by_cases h : () ∈ B
    · -- Case: () ∈ B, so D⁻¹'B = univ and B = univ (Unit has one element)
      have hpre : (fun (_ : ℝ) => ()) ⁻¹' B = Set.univ := by
        ext x; simp [h]
      have hB_univ : B = Set.univ := by ext ⟨⟩; simp [h]
      rw [hpre, hB_univ, Measure.restrict_univ, Measure.restrict_univ]
      -- Goal: ∫ f dμ = ∫ y, (∫ f d(κ y)) d(μ.map D)
      set μ := volume.restrict (Icc I.a I.b)
      -- Use Mathlib's Measure.map_const: μ.map (fun _ => c) = μ(univ) • dirac c
      rw [Measure.map_const, integral_smul_measure, integral_dirac, binKernel_integral]
      -- Goal: ∫ f dμ = (μ univ).toReal • binAverage f I
      simp only [binAverage, smul_eq_mul]
      have hpos : (0 : ℝ) < I.b - I.a := sub_pos.mpr I.hab
      have hmu : (μ Set.univ).toReal = I.b - I.a := by
        simp only [μ, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
        rw [Real.volume_Icc, ENNReal.toReal_ofReal hpos.le]
      rw [hmu]
      -- Goal: ∫ f dμ = (I.b - I.a) * (1 / (I.b - I.a) * ∫ x in I.a..I.b, f x)
      change ∫ (x : ℝ), f x ∂(volume.restrict (Icc I.a I.b)) = _
      rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le I.hab.le]
      field_simp
    · -- Case: () ∉ B, so B = ∅ (only element of Unit is ())
      have hB_empty : B = ∅ := by
        ext y; exact ⟨fun hy => absurd (Subsingleton.elim y () ▸ hy) h, False.elim⟩
      rw [hB_empty]
      simp [Set.preimage_empty, integral_zero_measure, Measure.restrict_empty]

/-!

### Connecting the Bridge to Bin Averages

Once the interval conditional kernel has been identified with normalized
restricted Lebesgue measure on each bin, the Kan value reduces to the
bin average. This is the concrete instantiation of the bridge theorem
from Part 4.
-/

/-- **The Kan value equals the bin average** (given a kernel that computes
bin averages).

This theorem shows that the abstract `lanValue` from the bridge theorem
specialises to the bin average when the conditional kernel is the bin
kernel. -/
theorem lanValue_eq_binAverage
    (f : ℝ → ℝ)
    (I : IntervalBin)
    (κ : Kernel Unit ℝ)
    (hκ : ∀ _u : Unit, (∫ x, f x ∂(κ ())) = binAverage f I) :
    lanValue (X := ℝObj) (Y := unitObj)
      (fun _x : ℝ => ()) measurable_const κ f () = binAverage f I := by
  simpa [lanValue] using hκ ()

/-- **The bin kernel satisfies the Kan value equation.** -/
theorem lanValue_eq_binAverage_of_binKernel
    (f : ℝ → ℝ) (I : IntervalBin) :
    lanValue (X := ℝObj) (Y := unitObj)
      (fun _x : ℝ => ()) measurable_const (binKernel I) f () = binAverage f I :=
  lanValue_eq_binAverage f I (binKernel I) (fun _ => binKernel_integral f I)

/-!

### Midpoint Quadrature Error Bound

The final application: the **midpoint rule** approximates the stochastic
Kan extension value to order `O(h²)`. This is the formal justification for
the midpoint quadrature used in IPM discretisation.

For a twice continuously differentiable function `f` on `[a, b]` with
`|f''(x)| ≤ M₂`, the classical error bound gives:

$$\left|\frac{1}{b-a}\int_a^b f(x)\,\mathrm{d}x - f\!\left(\frac{a+b}{2}\right)\right|
  \le \frac{M_2\,(b-a)^2}{24}$$

Combined with `lanValue_eq_binAverage`, this gives:

$$\left|(\text{Lan}_D\, f)(\star) - f(\text{midpoint})\right|
  \le \frac{M_2\, h^2}{24}$$

where `h = b - a` is the bin width. This is the error bound that ensures
IPM discretisations converge as the mesh is refined.
-/

/-- **Midpoint quadrature error bound.**

For a twice continuously differentiable function `f` on `[a, b]` with
`|f''(x)| ≤ M₂`, the midpoint rule error satisfies:

$$\left|\frac{1}{b-a}\int_a^b f(x)\,\mathrm{d}x - f\!\left(\frac{a+b}{2}\right)\right|
  \le \frac{M_2\,(b-a)^2}{24}$$

This is a classical result in numerical analysis (see e.g. Atkinson, *An Introduction
to Numerical Analysis*, §5.2). The standard proof proceeds as follows:

1. Set `m = (a+b)/2` and define the remainder `R(x) = f(x) - f(m) - f'(m)(x-m)`.
2. By the mean value theorem applied to `f'` (Lipschitz bound): `|f'(x) - f'(m)| ≤ M₂|x-m|`.
3. By the fundamental theorem of calculus applied twice (the `key` bound technique from
   Mathlib's `TrapezoidalRule.lean`): `|R(x)| ≤ M₂/2 · (x-m)²`.
4. By symmetry of the interval about `m`: `∫ₐᵇ f'(m)(x-m) dx = 0`.
5. Therefore `∫ₐᵇ (f(x)-f(m)) dx = ∫ₐᵇ R(x) dx`.
6. By the quadratic moment `∫ₐᵇ (x-m)² dx = (b-a)³/12`:
   `|∫ₐᵇ R(x) dx| ≤ M₂/2 · (b-a)³/12`.
7. Dividing by `(b-a)`: `|binAverage f I - f(m)| ≤ M₂(b-a)²/24`.

All steps are fully machine-checked below. Step 3 uses the
**iterated FTC technique**: the Convex MVT (`norm_image_sub_le_of_norm_derivWithin_le`)
gives the Lipschitz bound `|f'(t) - f'(m)| ≤ M₂·|t-m|`, then the
fundamental theorem of calculus (`intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le`)
converts `R(x) = ∫_m^x R'(t) dt`, and integral monotonicity + explicit
computation of `∫ M₂·|t-m| dt` yields the quadratic bound. The proof
handles both halves (`x ≥ m` and `x < m`) via separate FTC applications. -/
theorem midpoint_quadrature_error (I : IntervalBin) {f : ℝ → ℝ} {M₂ : ℝ}
    (hf : ContDiffOn ℝ 2 f (Icc I.a I.b))
    (hM : ∀ x ∈ Icc I.a I.b, |iteratedDerivWithin 2 f (Icc I.a I.b) x| ≤ M₂) :
    |binAverage f I - f I.midpoint| ≤ M₂ * (I.b - I.a) ^ 2 / 24 := by
  set a := I.a; set b := I.b; set m := I.midpoint
  have hab : a < b := I.hab
  have hba : (0 : ℝ) < b - a := sub_pos.mpr hab
  have hm : m = (a + b) / 2 := rfl
  -- Continuity and integrability
  have hf_cont : ContinuousOn f (Icc a b) :=
    (hf.differentiableOn two_ne_zero).continuousOn
  have hf_ii : IntervalIntegrable f volume a b := hf_cont.intervalIntegrable_of_Icc hab.le
  -- Remainder R(x) = f(x) - f(m) - f'(m)·(x - m)
  set f'm := derivWithin f (Icc a b) m
  set R := fun x ↦ f x - f m - f'm * (x - m)
  -- Continuity of R (needed for FTC in Step A)
  have hR_cont : ContinuousOn R (Icc a b) :=
    (hf_cont.sub continuousOn_const).sub
      (continuousOn_const.mul (continuousOn_id.sub continuousOn_const))
  -- Step A: Pointwise bound |R(x)| ≤ M₂/2·(x-m)² via iterated FTC
  have hR_pw : ∀ x ∈ Icc a b, |R x| ≤ M₂ / 2 * (x - m) ^ 2 := by
    have hud : UniqueDiffOn ℝ (Icc a b) := uniqueDiffOn_Icc hab
    have hf_diff : DifferentiableOn ℝ f (Icc a b) := hf.differentiableOn two_ne_zero
    have hf'_diff : DifferentiableOn ℝ (derivWithin f (Icc a b)) (Icc a b) :=
      (hf.derivWithin hud le_rfl).differentiableOn one_ne_zero
    have hf'_cont : ContinuousOn (derivWithin f (Icc a b)) (Icc a b) := hf'_diff.continuousOn
    have hm_mem : m ∈ Icc a b := ⟨by linarith, by linarith⟩
    -- Lipschitz bound on f': |f'(t) - f'(m)| ≤ M₂ * |t - m| (via Convex MVT)
    have hf'_lip : ∀ t ∈ Icc a b, |derivWithin f (Icc a b) t - f'm| ≤ M₂ * |t - m| := by
      intro t ht
      have hbound : ∀ y ∈ Icc a b,
          ‖derivWithin (derivWithin f (Icc a b)) (Icc a b) y‖ ≤ M₂ := by
        intro y hy
        simp only [show (2 : ℕ) = 1 + 1 from rfl, iteratedDerivWithin_succ'] at hM
        rw [Real.norm_eq_abs]; exact hM y hy
      have := Convex.norm_image_sub_le_of_norm_derivWithin_le hf'_diff hbound
        (convex_Icc a b) hm_mem ht
      rwa [Real.norm_eq_abs, Real.norm_eq_abs] at this
    set R' := fun t ↦ derivWithin f (Icc a b) t - f'm
    have hR'_cont : ContinuousOn R' (Icc a b) := hf'_cont.sub continuousOn_const
    -- HasDerivWithinAt for R: R'(t) = f'(t) - f'(m)
    have hR_deriv : ∀ t ∈ Icc a b, HasDerivWithinAt R (R' t) (Icc a b) t := by
      intro t ht
      have h1 := (hf_diff t ht).hasDerivWithinAt
      have h2 := (hasDerivWithinAt_const t (Icc a b) f'm).mul
        ((hasDerivWithinAt_id t (Icc a b)).sub (hasDerivWithinAt_const t (Icc a b) m))
      simp only [zero_mul, zero_add, mul_one, sub_zero] at h2
      have h3 := (h1.sub (hasDerivWithinAt_const t (Icc a b) (f m))).sub h2
      simp only [sub_zero] at h3
      exact h3.congr (fun x _ => by simp [R]) (by simp [R])
    have hR_m : R m = 0 := by simp [R]
    intro x hx
    by_cases hmx : m ≤ x
    · -- Right half: m ≤ x. FTC gives R(x) = ∫_m^x R'(t) dt.
      have hs : Icc m x ⊆ Icc a b := Icc_subset_Icc hm_mem.1 hx.2
      have hs' : Ioo m x ⊆ Ioo a b := Ioo_subset_Ioo hm_mem.1 hx.2
      have hR'_ii : IntervalIntegrable R' volume m x :=
        (hR'_cont.mono hs).intervalIntegrable_of_Icc hmx
      have hftc : ∫ t in m..x, R' t = R x := by
        have := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hmx (hR_cont.mono hs)
          (fun t ht ↦ (hR_deriv t (hs (Ioo_subset_Icc_self ht))).hasDerivAt
            (Icc_mem_nhds_iff.mpr (hs' ht))) hR'_ii
        linarith [hR_m]
      rw [← hftc]
      calc |∫ t in m..x, R' t|
        _ ≤ ∫ t in m..x, |R' t| := by
            rw [← Real.norm_eq_abs]
            exact intervalIntegral.norm_integral_le_integral_norm (μ := volume) hmx
        _ ≤ ∫ t in m..x, M₂ * (t - m) := by
            apply intervalIntegral.integral_mono_on hmx hR'_ii.abs
              (Continuous.intervalIntegrable (by fun_prop) m x)
            intro t ht
            calc |R' t| ≤ M₂ * |t - m| := hf'_lip t (hs ht)
              _ = M₂ * (t - m) := by congr 1; exact abs_of_nonneg (sub_nonneg.mpr ht.1)
        _ = M₂ / 2 * (x - m) ^ 2 := by
            have h := intervalIntegral.integral_comp_sub_right
              (a := m) (b := x) (f := fun t => M₂ * t) m
            simp only [sub_self] at h; rw [h]
            rw [show (fun t : ℝ => M₂ * t) = fun t => M₂ * t ^ (1 : ℕ) from by ext; simp]
            rw [intervalIntegral.integral_const_mul, integral_pow]; ring
    · -- Left half: x < m. FTC gives -R(x) = ∫_x^m R'(t) dt.
      push_neg at hmx
      have hxm := hmx.le
      have hs : Icc x m ⊆ Icc a b := Icc_subset_Icc hx.1 hm_mem.2
      have hs' : Ioo x m ⊆ Ioo a b := Ioo_subset_Ioo hx.1 hm_mem.2
      have hR'_ii : IntervalIntegrable R' volume x m :=
        (hR'_cont.mono hs).intervalIntegrable_of_Icc hxm
      have hftc : ∫ t in x..m, R' t = -(R x) := by
        have := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hxm (hR_cont.mono hs)
          (fun t ht ↦ (hR_deriv t (hs (Ioo_subset_Icc_self ht))).hasDerivAt
            (Icc_mem_nhds_iff.mpr (hs' ht))) hR'_ii
        rw [hR_m] at this; linarith
      rw [show R x = -(∫ t in x..m, R' t) from by linarith, abs_neg]
      calc |∫ t in x..m, R' t|
        _ ≤ ∫ t in x..m, |R' t| := by
            rw [← Real.norm_eq_abs]
            exact intervalIntegral.norm_integral_le_integral_norm (μ := volume) hxm
        _ ≤ ∫ t in x..m, M₂ * (m - t) := by
            apply intervalIntegral.integral_mono_on hxm hR'_ii.abs
              (Continuous.intervalIntegrable (by fun_prop) x m)
            intro t ht
            calc |R' t| ≤ M₂ * |t - m| := hf'_lip t (hs ht)
              _ = M₂ * (m - t) := by rw [abs_of_nonpos (sub_nonpos.mpr ht.2)]; ring
        _ = M₂ / 2 * (x - m) ^ 2 := by
            have h := intervalIntegral.integral_comp_sub_left
              (a := x) (b := m) (f := fun t => M₂ * t) m
            simp only [sub_self] at h; rw [h]
            rw [show (fun t : ℝ => M₂ * t) = fun t => M₂ * t ^ (1 : ℕ) from by ext; simp]
            rw [intervalIntegral.integral_const_mul, integral_pow]
            have hsq : (x - m) ^ 2 = (m - x) ^ 2 := by ring
            rw [hsq]; ring
  -- Step B: Integrability of R
  have hR_ii : IntervalIntegrable R volume a b := hR_cont.intervalIntegrable_of_Icc hab.le
  -- Step C: ∫(x - m) = 0 (symmetry)
  have symmetry : ∫ x in a..b, (x - m) = 0 := by
    have h := intervalIntegral.integral_comp_sub_right (a := a) (b := b) (f := fun x ↦ x) m
    have h' : ∫ x in a..b, (x - m) = ∫ x in a - m..b - m, x := h
    rw [h', show a - m = -(b - a) / 2 from by linarith,
        show b - m = (b - a) / 2 from by linarith]
    have h2 := integral_pow (a := -(b - a) / 2) (b := (b - a) / 2) 1
    simp only [pow_succ, pow_zero, one_mul, Nat.cast_one] at h2
    linarith
  -- Step D: ∫(x - m)² = (b-a)³/12 (quadratic moment)
  have moment : ∫ x in a..b, (x - m) ^ 2 = (b - a) ^ 3 / 12 := by
    have h := intervalIntegral.integral_comp_sub_right (a := a) (b := b) (f := fun x ↦ x ^ 2) m
    have h' : ∫ x in a..b, (x - m) ^ 2 = ∫ x in a - m..b - m, x ^ 2 := h
    rw [h', show a - m = -(b - a) / 2 from by linarith,
        show b - m = (b - a) / 2 from by linarith, integral_pow]
    ring
  -- Step E: binAverage - f(m) = 1/(b-a) · ∫ R
  have key_eq : binAverage f I - f m = (1 / (b - a)) * ∫ x in a..b, R x := by
    -- binAverage f I - f m = 1/(b-a) · ∫ f - f m
    -- ∫ (f - f m) = ∫ R + ∫ f'm*(x-m) = ∫ R + f'm * 0 = ∫ R
    have hfm_ii : IntervalIntegrable (fun x ↦ f'm * (x - m)) volume a b :=
      Continuous.intervalIntegrable (by fun_prop) a b
    have integral_R_eq : ∫ x in a..b, (f x - f m) = ∫ x in a..b, R x := by
      have h_sum : ∫ x in a..b, (f x - f m) =
          (∫ x in a..b, R x) + ∫ x in a..b, f'm * (x - m) := by
        rw [← intervalIntegral.integral_add hR_ii hfm_ii]
        exact intervalIntegral.integral_congr
          (fun x _ ↦ show f x - f m = R x + f'm * (x - m) by simp only [R]; ring)
      rw [h_sum, intervalIntegral.integral_const_mul, symmetry, mul_zero, add_zero]
    -- binAverage f I - f m = 1/(b-a) · ∫ f - f m = 1/(b-a) · ∫ R
    have h_avg : binAverage f I - f m = (1 / (b - a)) * ∫ x in a..b, (f x - f m) := by
      show (1 / (b - a)) * (∫ x in a..b, f x) - f m =
        (1 / (b - a)) * ∫ x in a..b, (f x - f m)
      rw [intervalIntegral.integral_sub hf_ii intervalIntegrable_const,
          intervalIntegral.integral_const, smul_eq_mul]
      field_simp
    rw [h_avg, integral_R_eq]
  -- Step F: Final bound
  rw [key_eq, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / (b - a))]
  have h_bound : |∫ x in a..b, R x| ≤ M₂ / 2 * ((b - a) ^ 3 / 12) := by
    have h_norm : |∫ x in a..b, R x| ≤ ∫ x in a..b, |R x| := by
      have := intervalIntegral.norm_integral_le_integral_norm (f := R) (μ := volume) hab.le
      rwa [Real.norm_eq_abs] at this
    calc |∫ x in a..b, R x|
      _ ≤ ∫ x in a..b, |R x| := h_norm
      _ ≤ ∫ x in a..b, M₂ / 2 * (x - m) ^ 2 := by
          apply intervalIntegral.integral_mono_on hab.le
            hR_ii.abs
            (Continuous.intervalIntegrable (by fun_prop) a b)
          exact fun x hx ↦ hR_pw x hx
      _ = M₂ / 2 * ((b - a) ^ 3 / 12) := by
          rw [intervalIntegral.integral_const_mul, moment]
  calc 1 / (b - a) * |∫ x in a..b, R x|
    _ ≤ 1 / (b - a) * (M₂ / 2 * ((b - a) ^ 3 / 12)) :=
        mul_le_mul_of_nonneg_left h_bound (by positivity)
    _ = M₂ * (b - a) ^ 2 / 24 := by field_simp; ring

/-- **Midpoint quadrature approximates the Kan value to O(h²).**

Given:
- `f` is `C²` on `[a, b]`
- `|f''(x)| ≤ M₂` on `[a, b]`
- `κ` computes bin averages

Then:
$$\left|(\text{Lan}_D\, f)(\star) - f(\text{midpoint})\right|
  \le \frac{M_2\,(b-a)^2}{24}$$

The smoothness hypotheses `hf` and `hM` are used via `midpoint_quadrature_error`,
which is fully machine-checked using the iterated FTC technique. -/
theorem midpoint_approximates_lanValue
    {f : ℝ → ℝ} (I : IntervalBin) {M₂ : ℝ}
    (hf : ContDiffOn ℝ 2 f (Icc I.a I.b))
    (hM : ∀ x ∈ Icc I.a I.b, |iteratedDerivWithin 2 f (Icc I.a I.b) x| ≤ M₂)
    (κ : Kernel Unit ℝ)
    (hκ : ∀ _u : Unit, (∫ x, f x ∂(κ ())) = binAverage f I) :
    |lanValue (X := ℝObj) (Y := unitObj)
      (fun _x : ℝ => ()) measurable_const κ f () - f I.midpoint|
      ≤ M₂ * (I.b - I.a) ^ 2 / 24 := by
  rw [lanValue_eq_binAverage f I κ hκ]
  exact midpoint_quadrature_error I hf hM

/-!

### The Bridge Connection

Combining `binKernel_isCondKernelMap` with `lanValue_isStochKanExtension`
from Part 4, we obtain a complete bridge: the bin average computed by
`lanValue` is a genuine **stochastic Kan extension** of any integrable
function along the trivial coarsening `ℝ → Unit`.

This closes the formalization loop:
```
binKernel_isCondKernelMap  →  IsCondKernelMap
                                    ↓
lanValue_isStochKanExtension  →  IsStochKanExtension
                                    ↓
ae_unique                   →  a.e. uniqueness
```
-/

/-- **The bin kernel gives a stochastic Kan extension.**

Combining `binKernel_isCondKernelMap` with `lanValue_isStochKanExtension`,
the `lanValue` computed from the bin kernel is a stochastic Kan extension
of any integrable function `f` along the trivial coarsening `D : ℝ → Unit`
with respect to `volume.restrict [a,b]`.

This is the complete bridge connection for the bin example: the abstract
categorical construction (Kan extension) and the concrete measure-theoretic
construction (bin average) are formally identified. -/
theorem isStochKanExtension_binKernel (I : IntervalBin) (f : ℝ → ℝ)
    (hf_meas : AEStronglyMeasurable f (volume.restrict (Icc I.a I.b)))
    (hf_int : Integrable f (volume.restrict (Icc I.a I.b))) :
    IsStochKanExtension (fun _ => ()) (volume.restrict (Icc I.a I.b))
      (lanValue (X := ℝObj) (Y := unitObj)
        (fun _ => ()) measurable_const (binKernel I) f) f :=
  lanValue_isStochKanExtension (X := ℝObj) (Y := unitObj)
    (fun _ => ()) measurable_const
    (volume.restrict (Icc I.a I.b))
    (binKernel I)
    (binKernel_isCondKernelMap I)
    f hf_meas hf_int

end CpmProofs
