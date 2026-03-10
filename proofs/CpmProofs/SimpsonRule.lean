import CpmProofs.NonUniformPartition
import CpmProofs.TrapezoidalRule

/-!

*Source: `SimpsonRule.lean`*

## Part 14: Higher-Order Quadrature — Simpson's Rule

Simpson's rule `S(f) = (f(a) + 4f(m) + f(b))/6` achieves `O(h⁴)` error
for `C⁴` functions — two orders better than midpoint or trapezoidal.

The error bound `M₄(b-a)⁴/720` is proved via 4th-order iterated FTC,
constructing the Taylor cubic remainder at the midpoint and bounding
the fourth-power moment integrals.

| # | Result | Status |
|---|--------|--------|
| 58 | Simpson average definition | ✅ |
| 59 | Simpson = 2/3 midpoint + 1/3 trapezoidal | ✅ |
| 60 | Simpson is exact for affine functions | ✅ |
| 61 | Per-cell O(h⁴) error bound | ✅ |
| 62 | Error bound with explicit hypothesis | ✅ |
| 63 | Composite Simpson error for non-uniform partitions | ✅ |
| 64 | Per-bin Simpson error (partition wrapper) | ✅ |
| 65 | Simpson O(h⁴) ≤ midpoint O(h²) for small h | ✅ |
| 66 | Composite Simpson vs midpoint comparison | ✅ |
| 67 | Simpson vs trapezoidal comparison | ✅ |
| 68 | Simpson kernel construction | ✅ |
| 69 | Integration against Simpson kernel | ✅ |
| 70 | Kan extension via Simpson kernel | ✅ |
| 71 | Simpson approximates the bin-average Kan value | ✅ |
| 72 | Convergence rate for uniform refinement | ✅ |
-/

open MeasureTheory
open ProbabilityTheory
open Set
open Finset

namespace CpmProofs

/-!

### Simpson's Rule Approximation
-/

/-- **Simpson's rule approximation of the bin average.**

$$S(f) = \frac{f(a) + 4\,f(m) + f(b)}{6}$$ -/
noncomputable def simpsonAverage (f : ℝ → ℝ) (I : IntervalBin) : ℝ :=
  (f I.a + 4 * f I.midpoint + f I.b) / 6

/-- **Simpson = 2/3 midpoint + 1/3 trapezoidal.** -/
theorem simpsonAverage_eq_weighted (f : ℝ → ℝ) (I : IntervalBin) :
    simpsonAverage f I = (2 / 3) * f I.midpoint + (1 / 3) * trapezoidalAverage f I := by
  simp only [simpsonAverage, trapezoidalAverage]
  ring

/-- **Simpson is exact for affine functions.** -/
theorem simpsonAverage_affine (I : IntervalBin) (c₀ c₁ : ℝ) :
    simpsonAverage (fun x => c₀ + c₁ * x) I = binAverage (fun x => c₀ + c₁ * x) I := by
  simp only [simpsonAverage, IntervalBin.midpoint, binAverage]
  have hba : (0 : ℝ) < I.b - I.a := sub_pos.mpr I.hab
  have h_int : ∫ x in I.a..I.b, (c₀ + c₁ * x) =
      c₀ * (I.b - I.a) + c₁ * ((I.b ^ 2 - I.a ^ 2) / 2) := by
    rw [show (fun x => c₀ + c₁ * x) =
        fun x => (fun _ => c₀) x + (fun x => c₁ * x ^ (1 : ℕ)) x from by
      ext x; simp]
    rw [intervalIntegral.integral_add intervalIntegrable_const
        (Continuous.intervalIntegrable (by fun_prop) I.a I.b)]
    rw [intervalIntegral.integral_const, smul_eq_mul,
        intervalIntegral.integral_const_mul, integral_pow]
    push_cast
    ring
  rw [h_int]
  field_simp
  ring

/-!

### Iterated FTC Helper

A general lemma for bounding functions via the Fundamental Theorem of
Calculus: if `g(m) = 0` and `|g'(t)| ≤ C · |t - m|^k`, then
`|g(x)| ≤ C/(k+1) · |x - m|^(k+1)`.
-/

private lemma ftc_power_bound
    {a b m : ℝ} (_hab : a < b) (hm : m ∈ Icc a b)
    {g g' : ℝ → ℝ} {C : ℝ} {k : ℕ}
    (_hC : 0 ≤ C)
    (hg_cont : ContinuousOn g (Icc a b))
    (hg'_cont : ContinuousOn g' (Icc a b))
    (hgm : g m = 0)
    (hg_deriv : ∀ t ∈ Icc a b, HasDerivWithinAt g (g' t) (Icc a b) t)
    (hg'_bound : ∀ t ∈ Icc a b, |g' t| ≤ C * |t - m| ^ k) :
    ∀ x ∈ Icc a b, |g x| ≤ C / (↑k + 1) * |x - m| ^ (k + 1) := by
  intro x hx
  by_cases hmx : m ≤ x
  · -- Right half: m ≤ x
    have hs : Icc m x ⊆ Icc a b := Icc_subset_Icc hm.1 hx.2
    have hs' : Ioo m x ⊆ Ioo a b := Ioo_subset_Ioo hm.1 hx.2
    have hg'_ii : IntervalIntegrable g' volume m x :=
      (hg'_cont.mono hs).intervalIntegrable_of_Icc hmx
    have hftc : ∫ t in m..x, g' t = g x := by
      have := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hmx (hg_cont.mono hs)
        (fun t ht ↦ (hg_deriv t (hs (Ioo_subset_Icc_self ht))).hasDerivAt
          (Icc_mem_nhds_iff.mpr (hs' ht))) hg'_ii
      linarith [hgm]
    rw [← hftc]
    calc |∫ t in m..x, g' t|
      _ ≤ ∫ t in m..x, |g' t| := by
          rw [← Real.norm_eq_abs]
          exact intervalIntegral.norm_integral_le_integral_norm (μ := volume) hmx
      _ ≤ ∫ t in m..x, C * (t - m) ^ k := by
          apply intervalIntegral.integral_mono_on hmx hg'_ii.abs
            (Continuous.intervalIntegrable (by fun_prop) m x)
          intro t ht
          calc |g' t| ≤ C * |t - m| ^ k := hg'_bound t (hs ht)
            _ = C * (t - m) ^ k := by
                congr 1; rw [abs_of_nonneg (sub_nonneg.mpr ht.1)]
      _ = C / (↑k + 1) * (x - m) ^ (k + 1) := by
          rw [intervalIntegral.integral_const_mul]
          have hsub : ∫ t in m..x, (t - m) ^ k = ∫ u in 0..(x - m), u ^ k := by
            have h := intervalIntegral.integral_comp_add_right
              (a := (0 : ℝ)) (b := x - m) (fun t => (t - m) ^ k) m
            simp only [show (0 : ℝ) + m = m from by ring,
                        show x - m + m = x from by ring,
                        show ∀ u : ℝ, u + m - m = u from fun u => by ring] at h
            exact h.symm
          rw [hsub, integral_pow, zero_pow (Nat.succ_ne_zero k), sub_zero]; ring
      _ = C / (↑k + 1) * |x - m| ^ (k + 1) := by
          congr 1; rw [abs_of_nonneg (sub_nonneg.mpr hmx)]
  · -- Left half: x < m
    push_neg at hmx
    have hxm := hmx.le
    have hs : Icc x m ⊆ Icc a b := Icc_subset_Icc hx.1 hm.2
    have hs' : Ioo x m ⊆ Ioo a b := Ioo_subset_Ioo hx.1 hm.2
    have hg'_ii : IntervalIntegrable g' volume x m :=
      (hg'_cont.mono hs).intervalIntegrable_of_Icc hxm
    have hftc : ∫ t in x..m, g' t = -(g x) := by
      have := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hxm (hg_cont.mono hs)
        (fun t ht ↦ (hg_deriv t (hs (Ioo_subset_Icc_self ht))).hasDerivAt
          (Icc_mem_nhds_iff.mpr (hs' ht))) hg'_ii
      rw [hgm] at this; linarith
    rw [show g x = -(∫ t in x..m, g' t) from by linarith, abs_neg]
    calc |∫ t in x..m, g' t|
      _ ≤ ∫ t in x..m, |g' t| := by
          rw [← Real.norm_eq_abs]
          exact intervalIntegral.norm_integral_le_integral_norm (μ := volume) hxm
      _ ≤ ∫ t in x..m, C * (m - t) ^ k := by
          apply intervalIntegral.integral_mono_on hxm hg'_ii.abs
            (Continuous.intervalIntegrable (by fun_prop) x m)
          intro t ht
          calc |g' t| ≤ C * |t - m| ^ k := hg'_bound t (hs ht)
            _ = C * (m - t) ^ k := by
                congr 1; rw [abs_of_nonpos (sub_nonpos.mpr ht.2), neg_sub]
      _ = C / (↑k + 1) * (m - x) ^ (k + 1) := by
          rw [intervalIntegral.integral_const_mul]
          have hsub : ∫ t in x..m, (m - t) ^ k = ∫ u in 0..(m - x), u ^ k := by
            have h := intervalIntegral.integral_comp_sub_left
              (a := x) (b := m) (fun u => u ^ k) m
            simp only [sub_self] at h
            exact h
          rw [hsub, integral_pow, zero_pow (Nat.succ_ne_zero k), sub_zero]; ring
      _ = C / (↑k + 1) * |x - m| ^ (k + 1) := by
          congr 1
          rw [abs_sub_comm x m, abs_of_nonneg (sub_nonneg.mpr hxm)]

/-!

### Per-Cell Error Bounds
-/

/-- **Per-cell Simpson error bound: O(h⁴).**

For a `C⁴` function `f` on `[a, b]` with `|f⁴(x)| ≤ M₄`:
$$\left|\text{binAverage}(f, I) - S(f, I)\right| \le \frac{M_4\,(b-a)^4}{720}$$

The proof extends the iterated FTC technique from order 2 (Part 5) to
order 4: the Taylor cubic remainder `R` at the midpoint satisfies
`|R(x)| ≤ M₄/24 · (x-m)⁴`, and the combined integral and endpoint
errors give the `1/720` constant via `1/1920 + 1/1152 = 1/720`. -/
theorem simpson_quadrature_error (I : IntervalBin) {f : ℝ → ℝ} {M₄ : ℝ}
    (hf : ContDiffOn ℝ 4 f (Icc I.a I.b))
    (hM : ∀ x ∈ Icc I.a I.b,
      |iteratedDerivWithin 4 f (Icc I.a I.b) x| ≤ M₄) :
    |binAverage f I - simpsonAverage f I| ≤ M₄ * (I.b - I.a) ^ 4 / 720 := by
  set a := I.a; set b := I.b; set m := I.midpoint
  set S := Icc a b
  have hab : a < b := I.hab
  have hba : (0 : ℝ) < b - a := sub_pos.mpr hab
  have hm : m = (a + b) / 2 := rfl
  have hm_mem : m ∈ S := ⟨by linarith, by linarith⟩
  have hud : UniqueDiffOn ℝ S := uniqueDiffOn_Icc hab
  -- Extract smoothness and differentiability at each level
  have hf_cont : ContinuousOn f S := (hf.differentiableOn (by norm_cast)).continuousOn
  have hf_ii : IntervalIntegrable f volume a b := hf_cont.intervalIntegrable_of_Icc hab.le
  have hf_diff : DifferentiableOn ℝ f S := hf.differentiableOn (by norm_cast)
  -- f' = derivWithin f S
  set f' := derivWithin f S with hf'_def
  have hf'_smooth : ContDiffOn ℝ 3 f' S := hf.derivWithin hud le_rfl
  have hf'_diff : DifferentiableOn ℝ f' S := hf'_smooth.differentiableOn (by norm_cast)
  have hf'_cont : ContinuousOn f' S := hf'_diff.continuousOn
  -- f'' = derivWithin f' S
  set f'' := derivWithin f' S with hf''_def
  have hf''_smooth : ContDiffOn ℝ 2 f'' S := hf'_smooth.derivWithin hud le_rfl
  have hf''_diff : DifferentiableOn ℝ f'' S := hf''_smooth.differentiableOn (by norm_cast)
  have hf''_cont : ContinuousOn f'' S := hf''_diff.continuousOn
  -- f''' = derivWithin f'' S
  set f''' := derivWithin f'' S with hf'''_def
  have hf'''_smooth : ContDiffOn ℝ 1 f''' S := hf''_smooth.derivWithin hud le_rfl
  have hf'''_diff : DifferentiableOn ℝ f''' S := hf'''_smooth.differentiableOn one_ne_zero
  have hf'''_cont : ContinuousOn f''' S := hf'''_diff.continuousOn
  -- Connect iteratedDerivWithin 4 to derivWithin f''' S
  have hM' : ∀ x ∈ S, ‖derivWithin f''' S x‖ ≤ M₄ := by
    intro x hx
    simp only [show (4 : ℕ) = ((0 + 1) + 1 + 1) + 1 from rfl,
      iteratedDerivWithin_succ', iteratedDerivWithin_zero] at hM
    rw [Real.norm_eq_abs]; exact hM x hx
  -- Level 0: Lipschitz bound |f'''(t) - f'''(m)| ≤ M₄ · |t - m|
  have hf'''_lip : ∀ t ∈ S, |f''' t - f''' m| ≤ M₄ * |t - m| := by
    intro t ht
    have := Convex.norm_image_sub_le_of_norm_derivWithin_le hf'''_diff hM'
      (convex_Icc a b) hm_mem ht
    rwa [Real.norm_eq_abs, Real.norm_eq_abs] at this
  -- Define Taylor cubic remainder at midpoint
  set R := fun x ↦ f x - f m - f' m * (x - m) - f'' m / 2 * (x - m) ^ 2
    - f''' m / 6 * (x - m) ^ 3
  -- Pointwise bound |R(x)| ≤ M₄/24 · (x - m)⁴ via 3 applications of ftc_power_bound
  have hR_pw : ∀ x ∈ S, |R x| ≤ M₄ / 24 * (x - m) ^ 4 := by
    -- Level 1: E₂(x) = f''(x) - f''(m) - f'''(m)(x-m), |E₂| ≤ M₄/2·|x-m|²
    set E₂ := fun x ↦ f'' x - f'' m - f''' m * (x - m)
    have hE₂_cont : ContinuousOn E₂ S :=
      (hf''_cont.sub continuousOn_const).sub
        (continuousOn_const.mul (continuousOn_id.sub continuousOn_const))
    have hE₂_m : E₂ m = 0 := by simp [E₂]
    set E₂' := fun t ↦ f''' t - f''' m
    have hE₂'_cont : ContinuousOn E₂' S := hf'''_cont.sub continuousOn_const
    have hE₂_deriv : ∀ t ∈ S, HasDerivWithinAt E₂ (E₂' t) S t := by
      intro t ht
      have h1 := (hf''_diff t ht).hasDerivWithinAt
      have h2 := hasDerivWithinAt_const t S (f'' m)
      have h_mul : HasDerivWithinAt (fun x => f''' m * (x - m)) (f''' m) S t := by
        have := (hasDerivWithinAt_const t S (f''' m)).mul
          ((hasDerivWithinAt_id t S).sub (hasDerivWithinAt_const t S m))
        simpa using this
      exact ((h1.sub h2).sub h_mul).congr_deriv
        (by rw [sub_zero, show derivWithin f'' S t = f''' t from by rw [← hf'''_def]])
    have hM₄_nn : 0 ≤ M₄ := le_trans (abs_nonneg _) (hM m hm_mem)
    have hE₂_pw : ∀ x ∈ S, |E₂ x| ≤ M₄ / 2 * |x - m| ^ 2 := by
      intro x hx
      have := ftc_power_bound hab hm_mem hM₄_nn
        hE₂_cont hE₂'_cont hE₂_m hE₂_deriv
        (fun t ht ↦ by rw [pow_one]; exact hf'''_lip t ht) x hx
      simp only [Nat.cast_one] at this; linarith
    -- Level 2: E₁(x) = f'(x) - f'(m) - f''(m)(x-m) - f'''(m)/2·(x-m)², |E₁| ≤ M₄/6·|x-m|³
    set E₁ := fun x ↦ f' x - f' m - f'' m * (x - m) - f''' m / 2 * (x - m) ^ 2
    have hE₁_cont : ContinuousOn E₁ S :=
      ((hf'_cont.sub continuousOn_const).sub
        (continuousOn_const.mul (continuousOn_id.sub continuousOn_const))).sub
        (continuousOn_const.mul ((continuousOn_id.sub continuousOn_const).pow 2))
    have hE₁_m : E₁ m = 0 := by simp [E₁]
    have hE₁_deriv : ∀ t ∈ S, HasDerivWithinAt E₁ (E₂ t) S t := by
      intro t ht
      have h1 := (hf'_diff t ht).hasDerivWithinAt
      have h2 := hasDerivWithinAt_const t S (f' m)
      have h3 := (hasDerivWithinAt_const t S (f'' m)).mul
        ((hasDerivWithinAt_id t S).sub (hasDerivWithinAt_const t S m))
      simp only [mul_one, sub_zero, zero_mul, zero_add] at h3
      have hxm_deriv : HasDerivWithinAt (fun x ↦ (x - m) ^ 2) (2 * (t - m)) S t := by
        have := ((hasDerivWithinAt_id t S).sub (hasDerivWithinAt_const t S m)).pow 2
        simpa using this
      have h4 := (hasDerivWithinAt_const t S (f''' m / 2)).mul hxm_deriv
      simp only [zero_mul, zero_add] at h4
      have goal := ((h1.sub h2).sub h3).sub h4
      convert goal using 1
      simp [E₂]; ring
    have hE₁_pw : ∀ x ∈ S, |E₁ x| ≤ M₄ / 6 * |x - m| ^ 3 := by
      intro x hx
      have := ftc_power_bound hab hm_mem (by positivity) hE₁_cont hE₂_cont hE₁_m hE₁_deriv hE₂_pw x hx
      push_cast at this; linarith
    -- Level 3: R(x), |R| ≤ M₄/24·|x-m|⁴
    have hR_cont : ContinuousOn R S :=
      (((hf_cont.sub continuousOn_const).sub
        (continuousOn_const.mul (continuousOn_id.sub continuousOn_const))).sub
        (continuousOn_const.mul ((continuousOn_id.sub continuousOn_const).pow 2))).sub
        (continuousOn_const.mul ((continuousOn_id.sub continuousOn_const).pow 3))
    have hR_m : R m = 0 := by simp [R]
    have hR_deriv : ∀ t ∈ S, HasDerivWithinAt R (E₁ t) S t := by
      intro t ht
      have h1 := (hf_diff t ht).hasDerivWithinAt
      have h2 := hasDerivWithinAt_const t S (f m)
      have h3 := (hasDerivWithinAt_const t S (f' m)).mul
        ((hasDerivWithinAt_id t S).sub (hasDerivWithinAt_const t S m))
      simp only [mul_one, sub_zero, zero_mul, zero_add] at h3
      have hxm_deriv2 : HasDerivWithinAt (fun x ↦ (x - m) ^ 2) (2 * (t - m)) S t := by
        have := ((hasDerivWithinAt_id t S).sub (hasDerivWithinAt_const t S m)).pow 2
        simpa using this
      have h4 := (hasDerivWithinAt_const t S (f'' m / 2)).mul hxm_deriv2
      simp only [zero_mul, zero_add] at h4
      have hxm_deriv3 : HasDerivWithinAt (fun x ↦ (x - m) ^ 3) (3 * (t - m) ^ 2) S t := by
        have := ((hasDerivWithinAt_id t S).sub (hasDerivWithinAt_const t S m)).pow 3
        simpa using this
      have h5 := (hasDerivWithinAt_const t S (f''' m / 6)).mul hxm_deriv3
      simp only [zero_mul, zero_add] at h5
      have goal := (((h1.sub h2).sub h3).sub h4).sub h5
      convert goal using 1
      simp [E₁]; ring
    have hR_pw' : ∀ x ∈ S, |R x| ≤ M₄ / 24 * |x - m| ^ 4 := by
      intro x hx
      have := ftc_power_bound hab hm_mem (by positivity) hR_cont hE₁_cont hR_m hR_deriv hE₁_pw x hx
      push_cast at this; linarith
    -- Convert |x - m|⁴ to (x - m)⁴ (even power)
    intro x hx
    have := hR_pw' x hx
    rwa [Even.pow_abs ⟨2, rfl⟩] at this
  -- Moment computations
  have moment1 : ∫ x in a..b, (x - m) = 0 := by
    have h := intervalIntegral.integral_comp_sub_right (a := a) (b := b) (f := fun x ↦ x) m
    rw [h, show a - m = -(b - a) / 2 from by linarith,
        show b - m = (b - a) / 2 from by linarith]
    have h2 := integral_pow (a := -(b - a) / 2) (b := (b - a) / 2) 1
    simp only [pow_succ, pow_zero, one_mul, Nat.cast_one] at h2; linarith
  have moment2 : ∫ x in a..b, (x - m) ^ 2 = (b - a) ^ 3 / 12 := by
    have h := intervalIntegral.integral_comp_sub_right (a := a) (b := b) (f := fun x ↦ x ^ 2) m
    rw [h, show a - m = -(b - a) / 2 from by linarith,
        show b - m = (b - a) / 2 from by linarith, integral_pow]; ring
  have moment3 : ∫ x in a..b, (x - m) ^ 3 = 0 := by
    have h := intervalIntegral.integral_comp_sub_right (a := a) (b := b) (f := fun x ↦ x ^ 3) m
    rw [h, show a - m = -(b - a) / 2 from by linarith,
        show b - m = (b - a) / 2 from by linarith, integral_pow]; ring
  have moment4 : ∫ x in a..b, (x - m) ^ 4 = (b - a) ^ 5 / 80 := by
    have h := intervalIntegral.integral_comp_sub_right (a := a) (b := b) (f := fun x ↦ x ^ 4) m
    rw [h, show a - m = -(b - a) / 2 from by linarith,
        show b - m = (b - a) / 2 from by linarith, integral_pow]; ring
  -- Key equation: binAverage f I - simpsonAverage f I = 1/(b-a)·∫R - (R(a)+R(b))/6
  -- This follows from: ∫P₃ = (b-a)·[f(m) + f''(m)·(b-a)²/24] and
  -- S(P₃) = f(m) + f''(m)·(b-a)²/24, so their contributions cancel.
  have hR_ii : IntervalIntegrable R volume a b := by
    apply ContinuousOn.intervalIntegrable_of_Icc (le_of_lt hab)
    exact (((hf_cont.sub continuousOn_const).sub
      (continuousOn_const.mul (continuousOn_id.sub continuousOn_const))).sub
      (continuousOn_const.mul ((continuousOn_id.sub continuousOn_const).pow 2))).sub
      (continuousOn_const.mul ((continuousOn_id.sub continuousOn_const).pow 3))
  -- Integrability of polynomial terms
  have hpoly1_ii : IntervalIntegrable (fun x ↦ f' m * (x - m)) volume a b :=
    Continuous.intervalIntegrable (by fun_prop) a b
  have hpoly2_ii : IntervalIntegrable (fun x ↦ f'' m / 2 * (x - m) ^ 2) volume a b :=
    Continuous.intervalIntegrable (by fun_prop) a b
  have hpoly3_ii : IntervalIntegrable (fun x ↦ f''' m / 6 * (x - m) ^ 3) volume a b :=
    Continuous.intervalIntegrable (by fun_prop) a b
  -- Compute ∫f in terms of ∫R and polynomial moment integrals
  have integral_f_eq : ∫ x in a..b, f x =
      (∫ x in a..b, R x) + f m * (b - a) + f'' m / 2 * ((b - a) ^ 3 / 12) := by
    have h_decomp : ∀ x, f x = R x + f m + f' m * (x - m) + f'' m / 2 * (x - m) ^ 2
        + f''' m / 6 * (x - m) ^ 3 := by intro x; simp [R]; ring
    rw [show (fun x ↦ f x) = fun x ↦ R x + f m + f' m * (x - m) + f'' m / 2 * (x - m) ^ 2
        + f''' m / 6 * (x - m) ^ 3 from by ext x; exact h_decomp x]
    rw [intervalIntegral.integral_add
        (((hR_ii.add intervalIntegrable_const).add hpoly1_ii).add hpoly2_ii) hpoly3_ii,
      intervalIntegral.integral_add
        ((hR_ii.add intervalIntegrable_const).add hpoly1_ii) hpoly2_ii,
      intervalIntegral.integral_add (hR_ii.add intervalIntegrable_const) hpoly1_ii,
      intervalIntegral.integral_add hR_ii intervalIntegrable_const,
      intervalIntegral.integral_const, smul_eq_mul,
      intervalIntegral.integral_const_mul, moment1, mul_zero, add_zero,
      intervalIntegral.integral_const_mul, moment2,
      intervalIntegral.integral_const_mul, moment3, mul_zero, add_zero]
    ring
  -- Compute Simpson of f in terms of R and polynomial values
  have hRm : R m = 0 := by simp [R]
  have simpson_f_eq : simpsonAverage f I =
      f m + f'' m / 2 * ((b - a) ^ 2 / 12) + (R a + R b) / 6 := by
    simp only [simpsonAverage]
    -- f(a) = f(m) + f'(m)(a-m) + f''(m)/2·(a-m)² + f'''(m)/6·(a-m)³ + R(a)
    -- f(b) = f(m) + f'(m)(b-m) + f''(m)/2·(b-m)² + f'''(m)/6·(b-m)³ + R(b)
    -- f(m) = f(m) + 0 + 0 + 0 + R(m) = f(m) + 0
    have hfa : f a = f m + f' m * (a - m) + f'' m / 2 * (a - m) ^ 2
        + f''' m / 6 * (a - m) ^ 3 + R a := by simp [R]
    have hfb : f b = f m + f' m * (b - m) + f'' m / 2 * (b - m) ^ 2
        + f''' m / 6 * (b - m) ^ 3 + R b := by simp [R]
    rw [hfa, hfb]
    -- Simplify: a - m = -(b-a)/2, b - m = (b-a)/2
    have ham : a - m = -(b - a) / 2 := by linarith
    have hbm : b - m = (b - a) / 2 := by linarith
    rw [ham, hbm]; ring
  -- Now combine: binAvg - S = 1/(b-a)·∫R - (R(a)+R(b))/6
  have key_eq : binAverage f I - simpsonAverage f I =
      1 / (b - a) * (∫ x in a..b, R x) - (R a + R b) / 6 := by
    rw [simpson_f_eq]
    show 1 / (b - a) * (∫ x in a..b, f x) -
      (f m + f'' m / 2 * ((b - a) ^ 2 / 12) + (R a + R b) / 6) =
      1 / (b - a) * (∫ x in a..b, R x) - (R a + R b) / 6
    rw [integral_f_eq]; field_simp; ring
  -- Final bound via triangle inequality
  rw [key_eq]
  -- |1/(b-a)·∫R - (R(a)+R(b))/6| ≤ |1/(b-a)·∫R| + |(R(a)+R(b))/6|
  --   ≤ M₄(b-a)⁴/1920 + M₄(b-a)⁴/1152 = M₄(b-a)⁴/720
  have h_int_bound : |1 / (b - a) * ∫ x in a..b, R x| ≤ M₄ * (b - a) ^ 4 / 1920 := by
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / (b - a))]
    have h_norm : |∫ x in a..b, R x| ≤ ∫ x in a..b, |R x| := by
      have := intervalIntegral.norm_integral_le_integral_norm (f := R) (μ := volume) hab.le
      rwa [Real.norm_eq_abs] at this
    calc 1 / (b - a) * |∫ x in a..b, R x|
      _ ≤ 1 / (b - a) * (∫ x in a..b, M₄ / 24 * (x - m) ^ 4) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          calc |∫ x in a..b, R x|
            _ ≤ ∫ x in a..b, |R x| := h_norm
            _ ≤ ∫ x in a..b, M₄ / 24 * (x - m) ^ 4 := by
                apply intervalIntegral.integral_mono_on hab.le hR_ii.abs
                  (Continuous.intervalIntegrable (by fun_prop) a b)
                intro x hx; exact hR_pw x hx
      _ = M₄ * (b - a) ^ 4 / 1920 := by
          rw [intervalIntegral.integral_const_mul, moment4]; field_simp; ring
  have h_end_bound : |(R a + R b) / 6| ≤ M₄ * (b - a) ^ 4 / 1152 := by
    have hRa : |R a| ≤ M₄ / 24 * ((b - a) / 2) ^ 4 := by
      have := hR_pw a (left_mem_Icc.mpr hab.le)
      have hq : (a - m) ^ 4 = ((b - a) / 2) ^ 4 := by
        have h : a - m = -((b - a) / 2) := by linarith
        rw [h]; ring
      rw [hq] at this; exact this
    have hRb : |R b| ≤ M₄ / 24 * ((b - a) / 2) ^ 4 := by
      have := hR_pw b (right_mem_Icc.mpr hab.le)
      rw [show b - m = (b - a) / 2 from by linarith] at this; exact this
    have hRab : |R a + R b| ≤ M₄ * (b - a) ^ 4 / 192 := by
      have h := norm_add_le (R a) (R b)
      rw [Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs] at h
      linarith
    calc |(R a + R b) / 6| = |R a + R b| / 6 := by
            rw [abs_div, show |(6 : ℝ)| = 6 from abs_of_pos (by norm_num)]
      _ ≤ M₄ * (b - a) ^ 4 / 192 / 6 := div_le_div_of_nonneg_right hRab (by norm_num)
      _ = M₄ * (b - a) ^ 4 / 1152 := by ring
  -- Triangle inequality: |A - B| ≤ |A| + |B|
  have h_triangle : |1 / (b - a) * (∫ x in a..b, R x) - (R a + R b) / 6| ≤
      |1 / (b - a) * ∫ x in a..b, R x| + |(R a + R b) / 6| := by
    have := norm_sub_le (1 / (b - a) * ∫ x in a..b, R x) ((R a + R b) / 6)
    rwa [Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs] at this
  linarith [add_le_add h_int_bound h_end_bound]

/-- **Per-cell Simpson error with explicit bound hypothesis.** -/
theorem simpson_quadrature_error_of_hyp (I : IntervalBin) {f : ℝ → ℝ} {C : ℝ}
    (hC : |binAverage f I - simpsonAverage f I| ≤ C) :
    |binAverage f I - simpsonAverage f I| ≤ C := hC

/-!

### Non-Uniform Partition Error Bounds
-/

namespace Partition

/-- **Per-bin Simpson error for non-uniform partitions.** -/
theorem nu_simpson_error (P : Partition)
    {f : ℝ → ℝ} {M₄ : ℝ}
    (hf_bin : ∀ k : Fin P.N,
      ContDiffOn ℝ 4 f (Icc (P.bins k).a (P.bins k).b))
    (hM_bin : ∀ k : Fin P.N, ∀ x ∈ Icc (P.bins k).a (P.bins k).b,
      |iteratedDerivWithin 4 f (Icc (P.bins k).a (P.bins k).b) x| ≤ M₄)
    (k : Fin P.N) :
    |binAverage f (P.bins k) - simpsonAverage f (P.bins k)| ≤
      M₄ * (P.width k) ^ 4 / 720 :=
  simpson_quadrature_error (P.bins k) (hf_bin k) (hM_bin k)

/-- **Composite Simpson error for non-uniform partitions.**

$$\left|\sum_{k=0}^{N-1} h_k \cdot (\text{binAvg}_k - S_k)\right|
  \le \frac{M_4 \cdot h_{\max}^4 \cdot L}{720}$$ -/
theorem nu_simpson_composite_error (P : Partition)
    {f : ℝ → ℝ} {M₄ : ℝ}
    (hM₄ : 0 ≤ M₄)
    (hf_bin : ∀ k : Fin P.N,
      ContDiffOn ℝ 4 f (Icc (P.bins k).a (P.bins k).b))
    (hM_bin : ∀ k : Fin P.N, ∀ x ∈ Icc (P.bins k).a (P.bins k).b,
      |iteratedDerivWithin 4 f (Icc (P.bins k).a (P.bins k).b) x| ≤ M₄) :
    |∑ k : Fin P.N,
      (P.width k * (binAverage f (P.bins k) - simpsonAverage f (P.bins k)))| ≤
      M₄ * P.hMax ^ 4 * P.L / 720 := by
  calc |∑ k : Fin P.N,
        (P.width k * (binAverage f (P.bins k) - simpsonAverage f (P.bins k)))|
      ≤ ∑ k : Fin P.N,
        |P.width k * (binAverage f (P.bins k) - simpsonAverage f (P.bins k))| :=
          Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k : Fin P.N,
        (P.width k * |binAverage f (P.bins k) - simpsonAverage f (P.bins k)|) := by
          congr 1; ext k
          rw [abs_mul, abs_of_pos (P.width_pos k)]
    _ ≤ ∑ k : Fin P.N, (P.width k * (M₄ * (P.width k) ^ 4 / 720)) := by
          apply Finset.sum_le_sum
          intro k _
          exact mul_le_mul_of_nonneg_left (nu_simpson_error P hf_bin hM_bin k)
            (le_of_lt (P.width_pos k))
    _ ≤ ∑ k : Fin P.N, (P.width k * (M₄ * P.hMax ^ 4 / 720)) := by
          apply Finset.sum_le_sum
          intro k _
          apply mul_le_mul_of_nonneg_left _ (le_of_lt (P.width_pos k))
          apply div_le_div_of_nonneg_right _ (by norm_num : (0 : ℝ) < 720).le
          apply mul_le_mul_of_nonneg_left _ hM₄
          have hw := P.width_le_hMax k
          have hwp := le_of_lt (P.width_pos k)
          calc P.width k ^ 4
              = (P.width k * P.width k) * (P.width k * P.width k) := by ring
            _ ≤ (P.hMax * P.hMax) * (P.hMax * P.hMax) := by
                apply mul_le_mul
                · exact mul_le_mul hw hw hwp (le_trans hwp hw)
                · exact mul_le_mul hw hw hwp (le_trans hwp hw)
                · exact mul_nonneg hwp hwp
                · exact mul_nonneg (le_trans hwp hw) (le_trans hwp hw)
            _ = P.hMax ^ 4 := by ring
    _ = M₄ * P.hMax ^ 4 / 720 * ∑ k : Fin P.N, P.width k := by
          simp_rw [show ∀ k : Fin P.N, P.width k * (M₄ * P.hMax ^ 4 / 720) =
              (M₄ * P.hMax ^ 4 / 720) * P.width k from fun k => by ring]
          rw [← Finset.mul_sum]
    _ = M₄ * P.hMax ^ 4 / 720 * P.L := by
          rw [P.sum_widths]
    _ = M₄ * P.hMax ^ 4 * P.L / 720 := by ring

end Partition

/-!

### Comparison Theorems
-/

/-- **Simpson O(h⁴) ≤ midpoint O(h²) for small h.** -/
theorem simpson_error_le_midpoint_error (I : IntervalBin) {M₂ M₄ : ℝ}
    (_hM₂ : 0 ≤ M₂) (_hM₄ : 0 ≤ M₄)
    (hh : M₄ * (I.b - I.a) ^ 2 ≤ 30 * M₂) :
    M₄ * (I.b - I.a) ^ 4 / 720 ≤ M₂ * (I.b - I.a) ^ 2 / 24 := by
  have h2 : 0 ≤ (I.b - I.a) ^ 2 := sq_nonneg _
  have key : M₄ * (I.b - I.a) ^ 2 * (I.b - I.a) ^ 2 ≤ 30 * M₂ * (I.b - I.a) ^ 2 :=
    mul_le_mul_of_nonneg_right hh h2
  have lhs_eq : M₄ * (I.b - I.a) ^ 4 / 720 =
      M₄ * (I.b - I.a) ^ 2 * (I.b - I.a) ^ 2 / 720 := by ring
  have rhs_eq : M₂ * (I.b - I.a) ^ 2 / 24 =
      30 * M₂ * (I.b - I.a) ^ 2 / 720 := by ring
  linarith [div_le_div_of_nonneg_right key (show (0 : ℝ) ≤ 720 by norm_num)]

/-- **Composite Simpson vs midpoint comparison.** -/
theorem simpson_composite_vs_midpoint_composite (P : Partition) {M₂ M₄ : ℝ}
    (_hM₂ : 0 ≤ M₂) (_hM₄ : 0 ≤ M₄) (hL : 0 ≤ P.L)
    (hh : M₄ * P.hMax ^ 2 ≤ 30 * M₂) :
    M₄ * P.hMax ^ 4 * P.L / 720 ≤ M₂ * P.hMax ^ 2 * P.L / 24 := by
  have hL2 : 0 ≤ P.hMax ^ 2 * P.L := mul_nonneg (sq_nonneg _) hL
  have key : M₄ * P.hMax ^ 2 * (P.hMax ^ 2 * P.L) ≤
      30 * M₂ * (P.hMax ^ 2 * P.L) := mul_le_mul_of_nonneg_right hh hL2
  have lhs_eq : M₄ * P.hMax ^ 4 * P.L / 720 =
      M₄ * P.hMax ^ 2 * (P.hMax ^ 2 * P.L) / 720 := by ring
  have rhs_eq : M₂ * P.hMax ^ 2 * P.L / 24 =
      30 * M₂ * (P.hMax ^ 2 * P.L) / 720 := by ring
  linarith [div_le_div_of_nonneg_right key (show (0 : ℝ) ≤ 720 by norm_num)]

/-- **Simpson O(h⁴) ≤ trapezoidal O(h²) for small h.** -/
theorem simpson_error_le_trapezoidal_error (I : IntervalBin) {M₂ M₄ : ℝ}
    (_hM₂ : 0 ≤ M₂) (_hM₄ : 0 ≤ M₄)
    (hh : M₄ * (I.b - I.a) ^ 2 ≤ 60 * M₂) :
    M₄ * (I.b - I.a) ^ 4 / 720 ≤ M₂ * (I.b - I.a) ^ 2 / 12 := by
  have h2 : 0 ≤ (I.b - I.a) ^ 2 := sq_nonneg _
  have key : M₄ * (I.b - I.a) ^ 2 * (I.b - I.a) ^ 2 ≤ 60 * M₂ * (I.b - I.a) ^ 2 :=
    mul_le_mul_of_nonneg_right hh h2
  have lhs_eq : M₄ * (I.b - I.a) ^ 4 / 720 =
      M₄ * (I.b - I.a) ^ 2 * (I.b - I.a) ^ 2 / 720 := by ring
  have rhs_eq : M₂ * (I.b - I.a) ^ 2 / 12 =
      60 * M₂ * (I.b - I.a) ^ 2 / 720 := by ring
  linarith [div_le_div_of_nonneg_right key (show (0 : ℝ) ≤ 720 by norm_num)]

/-!

### Kernel Construction
-/

/-- **Simpson kernel.** -/
noncomputable def simpsonKernel (P : Partition) : Kernel (Fin P.N) ℝ where
  toFun k :=
    ENNReal.ofReal (1 / 6) • Measure.dirac (P.bins k).a +
    ENNReal.ofReal (4 / 6) • Measure.dirac (P.bins k).midpoint +
    ENNReal.ofReal (1 / 6) • Measure.dirac (P.bins k).b
  measurable' := measurable_of_finite _

/-- **Integration against the Simpson kernel equals the Simpson average.** -/
theorem simpsonKernel_integral (P : Partition) (f : ℝ → ℝ) (k : Fin P.N) :
    (∫ x, f x ∂(simpsonKernel P k)) = simpsonAverage f (P.bins k) := by
  show ∫ x, f x ∂((simpsonKernel P).toFun k) = simpsonAverage f (P.bins k)
  simp only [simpsonKernel, simpsonAverage]
  have hd : ∀ x : ℝ, Integrable f (Measure.dirac x) := fun x =>
    integrable_dirac ENNReal.coe_lt_top
  have hs : ∀ (x : ℝ) (r : ℝ), Integrable f (ENNReal.ofReal r • Measure.dirac x) :=
    fun x r => (hd x).smul_measure ENNReal.ofReal_ne_top
  rw [integral_add_measure ((hs _ _).add_measure (hs _ _)) (hs _ _),
      integral_add_measure (hs _ _) (hs _ _),
      integral_smul_measure, integral_smul_measure, integral_smul_measure,
      integral_dirac, integral_dirac, integral_dirac]
  simp only [smul_eq_mul]
  have h : ∀ (r : ℝ), 0 ≤ r → (ENNReal.ofReal r).toReal = r :=
    fun r hr => ENNReal.toReal_ofReal hr
  rw [h _ (by positivity), h _ (by positivity)]
  ring

/-!

### Kan Extension Connection
-/

/-- **Kan extension via the Simpson kernel.** -/
theorem simpson_lanValue (P : Partition) (f : ℝ → ℝ) (k : Fin P.N) :
    lanValue (X := ⟨ℝ, inferInstance⟩) (Y := finObj P.N)
      (fun _ => k) measurable_const (simpsonKernel P) f k =
      simpsonAverage f (P.bins k) := by
  simp only [lanValue]
  exact simpsonKernel_integral P f k

/-- **Simpson approximates the bin-average Kan extension value.** -/
theorem simpson_approximates_lanValue
    {f : ℝ → ℝ} (I : IntervalBin) {M₄ : ℝ}
    (hf : ContDiffOn ℝ 4 f (Icc I.a I.b))
    (hM : ∀ x ∈ Icc I.a I.b, |iteratedDerivWithin 4 f (Icc I.a I.b) x| ≤ M₄)
    (κ : Kernel Unit ℝ)
    (hκ : ∀ _u : Unit, (∫ x, f x ∂(κ ())) = binAverage f I) :
    |lanValue (X := ℝObj) (Y := unitObj)
      (fun _x : ℝ => ()) measurable_const κ f () - simpsonAverage f I|
      ≤ M₄ * (I.b - I.a) ^ 4 / 720 := by
  rw [lanValue_eq_binAverage f I κ hκ]
  exact simpson_quadrature_error I hf hM

/-!

### Convergence Rate
-/

/-- **Simpson convergence rate for uniform refinement: O(1/N⁴).** -/
theorem simpson_convergence_rate {M₄ L : ℝ} (hM₄ : 0 ≤ M₄) (hL : 0 < L)
    {N : ℕ} (hN : 0 < N) :
    ∀ P : Partition, P.L = L → P.N = N → P.hMax ≤ L / N →
      M₄ * P.hMax ^ 4 * P.L / 720 ≤ M₄ * L ^ 5 / (720 * ↑N ^ 4) := by
  intro P hPL hPN hPh
  rw [hPL]
  have hN' : (0 : ℝ) < ↑N := Nat.cast_pos.mpr hN
  have hLN : 0 < L / ↑N := div_pos hL hN'
  have hhp : 0 < P.hMax := P.hMax_pos
  calc M₄ * P.hMax ^ 4 * L / 720
      ≤ M₄ * (L / ↑N) ^ 4 * L / 720 := by
        apply div_le_div_of_nonneg_right _ (by norm_num : (0 : ℝ) < 720).le
        apply mul_le_mul_of_nonneg_right _ hL.le
        apply mul_le_mul_of_nonneg_left _ hM₄
        have hw := hPh; have hwp := le_of_lt hhp
        calc P.hMax ^ 4
            = (P.hMax * P.hMax) * (P.hMax * P.hMax) := by ring
          _ ≤ (L / ↑N * (L / ↑N)) * (L / ↑N * (L / ↑N)) := by
              apply mul_le_mul
              · exact mul_le_mul hw hw hwp hLN.le
              · exact mul_le_mul hw hw hwp hLN.le
              · exact mul_nonneg hwp hwp
              · exact mul_nonneg hLN.le hLN.le
          _ = (L / ↑N) ^ 4 := by ring
    _ = M₄ * L ^ 5 / (720 * ↑N ^ 4) := by
        field_simp

end CpmProofs
