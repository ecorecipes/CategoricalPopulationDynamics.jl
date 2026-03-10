import CpmProofs.BinExample

/-!

*Source: `CompositeError.lean`*

## Part 6: Composite Quadrature Error Bounds

In Part 5, we proved that the midpoint rule approximates the Kan extension
value on a *single* bin to `O(h²)`. In practice, the domain `[a, a + L]`
is divided into `N` equal subintervals (bins), and the total error is the
sum of per-bin errors.

This file formalises two forms of the **composite error bound**:

1. **`composite_quadrature_error_bound`**: If each of `N` bin errors is
   bounded by `C · (L/N)³`, then the total error is at most `C · L³ / N²`.
2. **`composite_error_oh2`**: Equivalently, with `h = L/N`, the total error
   is at most `C · L · h²`.

These are **purely algebraic** results: the hard analytical work (bounding
per-bin errors) was done in Part 5. Here we sum them using the triangle
inequality and simplify.

### Connection to IPMs

In integral projection models, the domain of the kernel `K(z', z)` is
divided into `N` bins of width `h`. The composite error bound guarantees
that the discretised matrix approximation converges at rate `O(h²)` =
`O(1/N²)` as the mesh is refined, assuming the kernel is `C²`.

### Uniform Partition

We also define `UniformPartition` — a partition of `[a, a + L]` into `N`
equal subintervals — and prove that each subinterval is a valid
`IntervalBin`, enabling the per-bin midpoint error bound from Part 5.

### Results

| # | Result | Status |
|---|--------|--------|
| 17 | Composite error bound (algebraic) | ✅ |
| 18 | Composite error bound (O(h²) form) | ✅ |
| 19 | Uniform partition gives valid bins | ✅ |
| 20 | Composite midpoint error for uniform partition | ✅ |
-/

open MeasureTheory
open Finset

namespace CpmProofs

/-!

### Algebraic Composite Error Bounds

These results are independent of any particular quadrature rule. They state
that if each of `N` subinterval errors is bounded by `C · h³`, then the
total error over all subintervals is `O(h²)`.
-/

/-- **Composite quadrature error bound (algebraic form).**

If each of `N` subinterval errors satisfies `|errors k| ≤ C · (L/N)³`,
then the total error satisfies:

$$\left|\sum_{k=0}^{N-1} \text{errors}_k\right| \le \frac{C \cdot L^3}{N^2}$$

Equivalently, this is `O(1/N²)` = `O(h²)` convergence.

The proof is purely algebraic:
1. Triangle inequality: `|∑ errors| ≤ ∑ |errors|`
2. Apply per-bin bound: `∑ |errors| ≤ N · C · (L/N)³`
3. Simplify: `N · C · (L/N)³ = C · L³ / N²` -/
theorem composite_quadrature_error_bound
    (N : ℕ) (hN : 0 < N) (C L : ℝ) (_hC : 0 ≤ C)
    (errors : ℕ → ℝ)
    (h_bound : ∀ k ∈ Finset.range N, |errors k| ≤ C * (L / ↑N) ^ 3) :
    |∑ k ∈ Finset.range N, errors k| ≤ C * L ^ 3 / ↑N ^ 2 := by
  have hN' : (0 : ℝ) < ↑N := Nat.cast_pos.mpr hN
  calc |∑ k ∈ Finset.range N, errors k|
      ≤ ∑ k ∈ Finset.range N, |errors k| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.range N, (C * (L / ↑N) ^ 3) := Finset.sum_le_sum h_bound
    _ = ↑N * (C * (L / ↑N) ^ 3) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ = C * L ^ 3 / ↑N ^ 2 := by
        field_simp

/-- **Composite quadrature error bound (O(h²) form).**

With `h = L/N`, the total error satisfies `|∑ errors| ≤ C · L · h²`.
This makes the `O(h²)` convergence rate explicit. -/
theorem composite_error_oh2
    (N : ℕ) (hN : 0 < N) (C L h : ℝ) (_hC : 0 ≤ C)
    (hh : h = L / ↑N)
    (errors : ℕ → ℝ)
    (h_bound : ∀ k ∈ Finset.range N, |errors k| ≤ C * h ^ 3) :
    |∑ k ∈ Finset.range N, errors k| ≤ C * L * h ^ 2 := by
  have hN' : (0 : ℝ) < ↑N := Nat.cast_pos.mpr hN
  calc |∑ k ∈ Finset.range N, errors k|
      ≤ ∑ k ∈ Finset.range N, |errors k| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.range N, (C * h ^ 3) := Finset.sum_le_sum h_bound
    _ = ↑N * (C * h ^ 3) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ = C * (↑N * h) * h ^ 2 := by ring
    _ = C * L * h ^ 2 := by
        subst hh; field_simp

/-!

### Uniform Partition

A `UniformPartition` divides `[a, a + L]` into `N` equal subintervals.
Each subinterval `[a + k·h, a + (k+1)·h]` where `h = L/N` forms a valid
`IntervalBin`.
-/

/-- A uniform partition of `[a, a + L]` into `N` equal bins. -/
structure UniformPartition where
  a : ℝ
  L : ℝ
  N : ℕ
  hL : 0 < L
  hN : 0 < N

namespace UniformPartition

/-- Bin width: `h = L / N`. -/
noncomputable def h (P : UniformPartition) : ℝ := P.L / P.N

/-- Left endpoint of the `k`-th bin. -/
noncomputable def left (P : UniformPartition) (k : ℕ) : ℝ := P.a + k * P.h

/-- Right endpoint of the `k`-th bin. -/
noncomputable def right (P : UniformPartition) (k : ℕ) : ℝ := P.a + (k + 1) * P.h

/-- The right endpoint of the last bin is `a + L`. -/
theorem right_last (P : UniformPartition) :
    P.right (P.N - 1) = P.a + P.L := by
  simp only [right, h]
  have hN' : (0 : ℝ) < ↑P.N := Nat.cast_pos.mpr P.hN
  have : (↑(P.N - 1) + 1 : ℝ) = ↑P.N := by
    rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr (Nat.pos_iff_ne_zero.mp P.hN))]
    simp
  rw [this]
  field_simp

theorem h_pos (P : UniformPartition) : 0 < P.h := by
  unfold h
  exact div_pos P.hL (Nat.cast_pos.mpr P.hN)

/-- Each subinterval of a uniform partition is a valid `IntervalBin`. -/
noncomputable def bin (P : UniformPartition) (k : ℕ) : IntervalBin where
  a := P.left k
  b := P.right k
  hab := by
    unfold left right
    linarith [P.h_pos]

/-- The width of each bin equals `h`. -/
theorem bin_width (P : UniformPartition) (k : ℕ) :
    (P.bin k).b - (P.bin k).a = P.h := by
  simp [bin, left, right]; ring

/-- The midpoint of the `k`-th bin. -/
theorem bin_midpoint (P : UniformPartition) (k : ℕ) :
    (P.bin k).midpoint = P.a + (k + 1/2) * P.h := by
  simp [bin, IntervalBin.midpoint, left, right]; ring

/-- The `k`-th bin is contained in `[a, a + L]` for `k < N`. -/
theorem bin_subset (P : UniformPartition) {k : ℕ} (hk : k < P.N) :
    Set.Icc (P.bin k).a (P.bin k).b ⊆ Set.Icc P.a (P.a + P.L) := by
  apply Set.Icc_subset_Icc
  · -- left ≥ a: a + k * h ≥ a since k * h ≥ 0
    simp [bin, left]
    exact mul_nonneg (Nat.cast_nonneg _) (le_of_lt P.h_pos)
  · -- right ≤ a + L: a + (k+1) * h ≤ a + L since (k+1) * h ≤ N * h = L
    simp [bin, right, h]
    have hN' : (0 : ℝ) < ↑P.N := Nat.cast_pos.mpr P.hN
    have : (↑k + 1) ≤ (↑P.N : ℝ) := by exact_mod_cast hk
    have hh : P.L / ↑P.N > 0 := div_pos P.hL hN'
    calc (↑k + 1) * (P.L / ↑P.N)
        ≤ ↑P.N * (P.L / ↑P.N) := by
          exact mul_le_mul_of_nonneg_right this hh.le
      _ = P.L := by field_simp

end UniformPartition

/-!

### Composite Midpoint Error

Combining the per-bin midpoint error (Part 5) with the algebraic composite
bound yields the full composite midpoint error for a uniform partition.

We state the composite bound assuming per-bin `ContDiffOn` and second-derivative
bounds are given directly, since the global-to-local implication for
`iteratedDerivWithin` on subsets involves technical Mathlib infrastructure
that is orthogonal to the main result.
-/

/-- **Composite midpoint error for a uniform partition.**

If each bin satisfies the hypotheses of `midpoint_quadrature_error` from
Part 5 (C² with |f''| ≤ M₂), then the total composite midpoint error
satisfies:

$$\left|\sum_{k=0}^{N-1} \left(\text{binAverage}(f, I_k) - f(m_k)\right)\right|
  \le \frac{M_2 \cdot N \cdot h^2}{24}$$

where `h = L/N` and `m_k` is the midpoint of the `k`-th bin.

In IPM applications, the relevant quantity is the weighted sum
`h · ∑(binAverage - f(midpoint))` representing the total integral error;
dividing by `(b-a)` gives the error per unit length. -/
theorem composite_midpoint_error (P : UniformPartition)
    {f : ℝ → ℝ} {M₂ : ℝ}
    (_hM₂ : 0 ≤ M₂)
    (hf_bin : ∀ k, k < P.N →
      ContDiffOn ℝ 2 f (Set.Icc (P.bin k).a (P.bin k).b))
    (hM_bin : ∀ k, k < P.N → ∀ x ∈ Set.Icc (P.bin k).a (P.bin k).b,
      |iteratedDerivWithin 2 f (Set.Icc (P.bin k).a (P.bin k).b) x| ≤ M₂) :
    |∑ k ∈ Finset.range P.N,
      (binAverage f (P.bin k) - f (P.bin k).midpoint)| ≤
      M₂ * P.N * P.h ^ 2 / 24 := by
  -- Per-bin error bound from Part 5
  have per_bin : ∀ k ∈ Finset.range P.N,
      |binAverage f (P.bin k) - f (P.bin k).midpoint| ≤ M₂ * P.h ^ 2 / 24 := by
    intro k hk
    have hk_lt : k < P.N := Finset.mem_range.mp hk
    have h_err := midpoint_quadrature_error (P.bin k) (hf_bin k hk_lt) (hM_bin k hk_lt)
    rw [P.bin_width k] at h_err
    exact h_err
  -- Sum the per-bin bounds
  calc |∑ k ∈ Finset.range P.N, (binAverage f (P.bin k) - f (P.bin k).midpoint)|
      ≤ ∑ k ∈ Finset.range P.N,
        |binAverage f (P.bin k) - f (P.bin k).midpoint| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.range P.N, (M₂ * P.h ^ 2 / 24) := Finset.sum_le_sum per_bin
    _ = ↑P.N * (M₂ * P.h ^ 2 / 24) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ = M₂ * ↑P.N * P.h ^ 2 / 24 := by ring

/-- **Composite midpoint error in O(h²) form.**

Substituting `N = L/h` into the composite bound gives:

$$\text{total error} \le \frac{M_2 \cdot L \cdot h^2}{24 \cdot h}
  = \frac{M_2 \cdot L}{24} \cdot h$$

Wait — this is `O(h)` for the *average* errors. The `O(h²)` bound applies
to the *integral* errors. Let us state the weighted version: the sum
`∑ h · (binAverage - f(midpoint))` (which approximates `∫ f - ∑ h·f(mₖ)`)
satisfies:

$$\left|\sum_{k=0}^{N-1} h \cdot (\text{binAverage} - f(m_k))\right|
  \le \frac{M_2 \cdot L \cdot h^2}{24}$$

This is the standard O(h²) composite midpoint convergence rate. -/
theorem composite_midpoint_integral_error (P : UniformPartition)
    {f : ℝ → ℝ} {M₂ : ℝ}
    (_hM₂ : 0 ≤ M₂)
    (hf_bin : ∀ k, k < P.N →
      ContDiffOn ℝ 2 f (Set.Icc (P.bin k).a (P.bin k).b))
    (hM_bin : ∀ k, k < P.N → ∀ x ∈ Set.Icc (P.bin k).a (P.bin k).b,
      |iteratedDerivWithin 2 f (Set.Icc (P.bin k).a (P.bin k).b) x| ≤ M₂) :
    |∑ k ∈ Finset.range P.N,
      (P.h * (binAverage f (P.bin k) - f (P.bin k).midpoint))| ≤
      M₂ * P.L * P.h ^ 2 / 24 := by
  -- Factor h out of the sum
  have h_factor : ∑ k ∈ Finset.range P.N,
      (P.h * (binAverage f (P.bin k) - f (P.bin k).midpoint)) =
      P.h * ∑ k ∈ Finset.range P.N,
        (binAverage f (P.bin k) - f (P.bin k).midpoint) := by
    rw [← Finset.mul_sum]
  rw [h_factor, abs_mul, abs_of_pos P.h_pos]
  have h_inner := composite_midpoint_error P _hM₂ hf_bin hM_bin
  calc P.h * |∑ k ∈ Finset.range P.N, (binAverage f (P.bin k) - f (P.bin k).midpoint)|
      ≤ P.h * (M₂ * ↑P.N * P.h ^ 2 / 24) :=
        mul_le_mul_of_nonneg_left h_inner (le_of_lt P.h_pos)
    _ = M₂ * (P.h * ↑P.N) * P.h ^ 2 / 24 := by ring
    _ = M₂ * P.L * P.h ^ 2 / 24 := by
        unfold UniformPartition.h
        have hN' : (↑P.N : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr P.hN)
        field_simp

end CpmProofs
