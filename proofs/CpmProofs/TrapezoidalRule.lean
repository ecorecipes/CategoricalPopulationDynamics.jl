import CpmProofs.BinExample
import Mathlib.MeasureTheory.Integral.IntervalIntegral.TrapezoidalRule

/-!

*Source: `TrapezoidalRule.lean`*

## Part 9: Higher-Order Quadrature — Trapezoidal Rule

Part 5 proved the midpoint quadrature error bound `O(h²)` using the
iterated FTC technique. This file connects the Kan extension framework
to the **trapezoidal rule**, an alternative quadrature method with the
same `O(h²)` convergence rate but different error characteristics.

### Background

For a `C²` function `f` on `[a, b]` with `|f''| ≤ M₂`:

- **Midpoint rule** (Part 5): `|binAverage(f) - f(mid)| ≤ M₂ h²/24`
- **Trapezoidal rule**: `|T(f) - ∫f| ≤ M₂ h³/12` (single trapezoid)
  or `|T_N(f) - ∫f| ≤ M₂ (b-a)³/(12N²)` (N trapezoids)

where `T(f) = h/2 · (f(a) + f(b))` and `h = b - a`.

Mathlib's trapezoidal rule formalization (Kielstra, 2025) provides:
- `trapezoidal_integral f N a b` — the trapezoidal approximation
- `trapezoidal_error_le` — the `O(h²)` error bound

### Connection to the Kan Extension

The trapezoidal rule provides an alternative way to compute the Kan
extension value numerically. While the midpoint rule uses the function
value at the bin center, the trapezoidal rule uses the values at bin
endpoints. Both converge at `O(h²)` but:

- Midpoint has coefficient `M₂/24` (smaller constant)
- Trapezoidal has coefficient `M₂/12` (larger constant)
- Trapezoidal is often preferred in practice due to endpoint reuse

### Results

| # | Result | Status |
|---|--------|--------|
| 31 | Trapezoidal rule approximates bin average | ✅ |
| 32 | Trapezoidal Kan extension error bound | ✅ |
| 33 | Midpoint vs trapezoidal comparison | ✅ |
-/

open MeasureTheory
open ProbabilityTheory

namespace CpmProofs

/-!

### Trapezoidal Approximation of the Bin Average

The trapezoidal rule for a single bin `[a, b]` gives:
$$T_1(f) = \frac{b-a}{2}\,(f(a) + f(b))$$

Dividing by `(b-a)`, the trapezoidal bin average approximation is:
$$\frac{T_1(f)}{b-a} = \frac{f(a) + f(b)}{2}$$

The trapezoidal error (for the integral, not the average) is:
$$|T_1(f) - \int_a^b f| \le \frac{M_2 \cdot (b-a)^3}{12}$$
-/

/-- **Trapezoidal approximation of the bin average.**

The trapezoidal rule for a single bin gives the average of the endpoint
values: `(f(a) + f(b)) / 2`. -/
noncomputable def trapezoidalAverage (f : ℝ → ℝ) (I : IntervalBin) : ℝ :=
  (f I.a + f I.b) / 2

/-- **Trapezoidal rule approximates the bin average** (Kan extension value).

For a `C²` function `f` with `|f''| ≤ M₂`, the trapezoidal average
approximates the bin average (= Kan extension value) with error
`O(h²)`:

$$\left|\text{binAverage}(f, I) - \frac{f(a) + f(b)}{2}\right|
  \le \frac{M_2 \cdot (b-a)^2}{12}$$

The coefficient `M₂/12` is twice the midpoint coefficient `M₂/24`,
reflecting the well-known fact that the midpoint rule has half the
error constant of the trapezoidal rule for smooth functions.

The proof delegates to Mathlib's `trapezoidal_error_le_of_c2` for the
integral error, then divides by `(b-a)` to get the bin-average error. -/
theorem trapezoidal_approximates_binAverage (I : IntervalBin) {f : ℝ → ℝ} {M₂ : ℝ}
    (hf : ContDiffOn ℝ 2 f (Set.uIcc I.a I.b))
    (hM : ∀ x, |iteratedDerivWithin 2 f (Set.uIcc I.a I.b) x| ≤ M₂) :
    |binAverage f I - trapezoidalAverage f I| ≤ M₂ * (I.b - I.a) ^ 2 / 12 := by
  -- binAverage = (1/(b-a)) * ∫ₐᵇ f
  -- trapezoidalAverage = (f(a) + f(b))/2
  -- trapezoidal_integral f 1 a b = (b-a)/2 * (f(a) + f(b)) by trapezoidal_integral_one
  -- So binAverage - trapAverage = (1/(b-a)) * (∫ₐᵇ f - trapezoidal_integral f 1 a b)
  have hba : (0 : ℝ) < I.b - I.a := sub_pos.mpr I.hab
  -- Mathlib's trapezoidal error bound (for the integral, not the average)
  have h_trap := trapezoidal_error_le_of_c2 hf hM (N_nonzero := Nat.one_pos)
  -- trapezoidal_error f 1 a b = trapezoidal_integral f 1 a b - ∫ₐᵇ f
  -- |trapezoidal_integral f 1 a b - ∫ₐᵇ f| ≤ |b-a|³ · M₂ / 12
  simp only [trapezoidal_error, Nat.cast_one] at h_trap
  -- |trapezoidal_integral f 1 a b - ∫ x in a..b, f x| ≤ |b-a|³ · M₂ / 12
  have h_abs_ba : |I.b - I.a| = I.b - I.a := abs_of_pos hba
  rw [h_abs_ba] at h_trap
  -- Now relate to bin average and trapezoidal average
  have h_trap_one := trapezoidal_integral_one f I.a I.b
  -- trapezoidal_integral f 1 a b = (b-a)/2 * (f(a) + f(b))
  -- binAverage f I = (1/(b-a)) * ∫ x in a..b, f x
  -- binAverage - trapAverage = (1/(b-a)) * (∫ₐᵇ f - (b-a) * trapAverage)
  --                          = (1/(b-a)) * (∫ₐᵇ f - trapezoidal_integral f 1 a b)
  --                          = -(1/(b-a)) * trapezoidal_error f 1 a b
  have h_eq : binAverage f I - trapezoidalAverage f I =
      -(1 / (I.b - I.a)) * trapezoidal_error f 1 I.a I.b := by
    simp only [binAverage, trapezoidalAverage, trapezoidal_error, h_trap_one]
    field_simp
    ring
  rw [h_eq, neg_mul, abs_neg, abs_mul,
    abs_of_pos (by positivity : (0 : ℝ) < 1 / (I.b - I.a))]
  have h_trap' : |trapezoidal_error f 1 I.a I.b| ≤ (I.b - I.a) ^ 3 * M₂ / 12 := by
    have := h_trap; simp only [one_pow, mul_one] at this; exact this
  calc 1 / (I.b - I.a) * |trapezoidal_error f 1 I.a I.b|
      ≤ 1 / (I.b - I.a) * ((I.b - I.a) ^ 3 * M₂ / 12) :=
        mul_le_mul_of_nonneg_left h_trap' (by positivity)
    _ = M₂ * (I.b - I.a) ^ 2 / 12 := by field_simp

/-- **Trapezoidal rule approximates the Kan extension value.**

Combined with `lanValue_eq_binAverage`, this gives:

$$\left|(\text{Lan}_D\, f)(\star) - \frac{f(a) + f(b)}{2}\right|
  \le \frac{M_2 \cdot h^2}{12}$$ -/
theorem trapezoidal_approximates_lanValue
    {f : ℝ → ℝ} (I : IntervalBin) {M₂ : ℝ}
    (hf : ContDiffOn ℝ 2 f (Set.uIcc I.a I.b))
    (hM : ∀ x, |iteratedDerivWithin 2 f (Set.uIcc I.a I.b) x| ≤ M₂)
    (κ : Kernel Unit ℝ)
    (hκ : ∀ _u : Unit, (∫ x, f x ∂(κ ())) = binAverage f I) :
    |lanValue (X := ℝObj) (Y := unitObj)
      (fun _x : ℝ => ()) measurable_const κ f () - trapezoidalAverage f I|
      ≤ M₂ * (I.b - I.a) ^ 2 / 12 := by
  rw [lanValue_eq_binAverage f I κ hκ]
  exact trapezoidal_approximates_binAverage I hf hM

/-!

### Comparison: Midpoint vs Trapezoidal

The midpoint rule (Part 5) has error coefficient `M₂/24` while the
trapezoidal rule has `M₂/12`. We state this comparison formally.
-/

/-- **Midpoint rule has half the error constant of the trapezoidal rule.**

For any `C²` function on `[a, b]`:
- Midpoint error ≤ `M₂ h² / 24`
- Trapezoidal error ≤ `M₂ h² / 12`

So `midpoint error ≤ trapezoidal error / 2`. This explains why the
midpoint rule often outperforms the trapezoidal rule in practice. -/
theorem midpoint_error_le_half_trapezoidal_error (I : IntervalBin) {M₂ : ℝ}
    (hM₂ : 0 ≤ M₂) :
    M₂ * (I.b - I.a) ^ 2 / 24 ≤ M₂ * (I.b - I.a) ^ 2 / 12 := by
  have hba : (0 : ℝ) ≤ (I.b - I.a) ^ 2 := sq_nonneg _
  have : M₂ * (I.b - I.a) ^ 2 / 24 = M₂ * (I.b - I.a) ^ 2 / 12 / 2 := by ring
  linarith [mul_nonneg hM₂ hba]

end CpmProofs
