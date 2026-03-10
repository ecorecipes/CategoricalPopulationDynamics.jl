import CpmProofs.MultiBin

/-!

*Source: `NonUniformPartition.lean`*

## Part 11: Non-Uniform Partitions

Parts 6–7 established composite error bounds and multi-bin Kan extensions
for **uniform** partitions (all bins have width `h = L/N`). In practice,
IPMs sometimes use **adaptive meshes** with variable-width bins concentrated
near regions of high curvature.

This file generalizes the formalization to non-uniform partitions:

1. A `Partition` structure with adjacency constraints on `Fin N → IntervalBin`.
2. Per-bin widths, maximum width `hMax`, and a telescoping sum proof.
3. A non-uniform kernel `nuKernel` that reduces to `binKernel` per bin.
4. Composite error bounds using `hMax` instead of uniform `h`.

### Key Insight

`midpoint_quadrature_error` already works for arbitrary-width intervals:
`|binAverage f I - f I.midpoint| ≤ M₂ * (I.b - I.a)² / 24`. The per-bin
error depends on `(b-a)²`, not on any global `h`. For non-uniform partitions,
the composite integral error is bounded by `M₂ * hMax² * L / 24` since each
`h_k² ≤ hMax²`.

### Results

| # | Result | Status |
|---|--------|--------|
| 35 | Partition structure with adjacency | ✅ |
| 36 | Bin widths positive, bounded by hMax | ✅ |
| 37 | Telescoping sum of widths = L | ✅ |
| 38 | Non-uniform kernel construction | ✅ |
| 39 | Composite error for non-uniform partitions | ✅ |
| 40 | Uniform partition embeds into Partition | ✅ |
-/

open MeasureTheory
open CategoryTheory
open ProbabilityTheory
open Finset
open Set

namespace CpmProofs

/-!

### The Partition Structure

A `Partition` divides `[a, a + L]` into `N` adjacent subintervals of
possibly different widths. Each bin is an `IntervalBin` (carrying its
own `hab : a < b` proof), and adjacency constraints ensure the bins
tile the interval without gaps or overlaps.
-/

/-- A (non-uniform) partition of `[a, a + L]` into `N` adjacent bins.

The adjacency condition ensures consecutive bins share endpoints:
`(bins i).b = (bins j).a` whenever `j = i + 1`. Combined with
`first_left` and `last_right`, the bins tile `[a, a + L]` exactly. -/
structure Partition where
  N : ℕ
  hN : 0 < N
  a : ℝ
  L : ℝ
  hL : 0 < L
  bins : Fin N → IntervalBin
  adjacency : ∀ (i j : Fin N), i.val + 1 = j.val → (bins i).b = (bins j).a
  first_left : (bins ⟨0, hN⟩).a = a
  last_right : (bins ⟨N - 1, by omega⟩).b = a + L

namespace Partition

/-!

### Bin Widths
-/

/-- Width of the `k`-th bin: `(bins k).b - (bins k).a`. -/
noncomputable def width (P : Partition) (k : Fin P.N) : ℝ :=
  (P.bins k).b - (P.bins k).a

/-- Each bin has positive width (from `IntervalBin.hab`). -/
theorem width_pos (P : Partition) (k : Fin P.N) : 0 < P.width k :=
  sub_pos.mpr (P.bins k).hab

/-!

### Maximum Bin Width
-/

/-- Maximum bin width across all bins, computed via `Finset.sup'`. -/
noncomputable def hMax (P : Partition) : ℝ :=
  Finset.sup' Finset.univ ⟨⟨0, P.hN⟩, Finset.mem_univ _⟩ (fun k => P.width k)

/-- The maximum bin width is positive. -/
theorem hMax_pos (P : Partition) : 0 < P.hMax := by
  unfold hMax
  have h := P.width_pos ⟨0, P.hN⟩
  calc 0 < P.width ⟨0, P.hN⟩ := h
    _ ≤ Finset.sup' Finset.univ ⟨⟨0, P.hN⟩, Finset.mem_univ _⟩ (fun k => P.width k) :=
        Finset.le_sup' _ (Finset.mem_univ _)

/-- Each bin width is at most `hMax`. -/
theorem width_le_hMax (P : Partition) (k : Fin P.N) : P.width k ≤ P.hMax :=
  Finset.le_sup' _ (Finset.mem_univ k)

/-!

### Telescoping Sum of Widths

The sum of all bin widths equals `L`. This is the most technically
challenging proof: we define a `node` function and use the adjacency
constraints to show that each width is a consecutive difference, then
apply `Finset.sum_range_sub'` (or equivalent) to telescope.
-/

/-- The left endpoint of the `k`-th bin, as a function on `Fin N`.
    Used internally for the telescoping sum proof. -/
private noncomputable def leftNode (P : Partition) (k : Fin P.N) : ℝ :=
  (P.bins k).a

/-- Adjacency implies the left endpoint of bin `j` equals the right
    endpoint of bin `i` when `j = i + 1`. -/
private theorem left_eq_right_succ (P : Partition) (i : Fin P.N) (j : Fin P.N)
    (hij : i.val + 1 = j.val) : (P.bins i).b = (P.bins j).a :=
  P.adjacency i j hij

/-- **Telescoping sum**: the sum of all bin widths equals `L`.

The proof constructs a `node` function `k ↦ (bins k).a` for `k < N`,
extended to `node N = a + L`. Each `width k = node (k+1) - node k`
by adjacency, and the sum telescopes to `node N - node 0 = (a+L) - a = L`. -/
theorem sum_widths (P : Partition) :
    ∑ k : Fin P.N, P.width k = P.L := by
  -- Define node : ℕ → ℝ where node k = (bins k).a for k < N, node N = a + L
  set node : ℕ → ℝ := fun k =>
    if h : k < P.N then (P.bins ⟨k, h⟩).a else P.a + P.L
  -- Show width k = node (k+1) - node k
  have h_width : ∀ k : Fin P.N, P.width k = node (k.val + 1) - node k.val := by
    intro ⟨k, hk⟩
    simp only [width, node]
    -- node k = (bins k).a since k < N
    rw [dif_pos hk]
    -- For node (k+1): case split on k+1 < N
    by_cases hk1 : k + 1 < P.N
    · -- k+1 < N: node (k+1) = (bins (k+1)).a = (bins k).b by adjacency
      rw [dif_pos hk1]
      have := P.adjacency ⟨k, hk⟩ ⟨k + 1, hk1⟩ rfl
      linarith
    · -- k+1 = N (since k < N): node (k+1) = a + L = (bins (N-1)).b
      rw [dif_neg hk1]
      have hkN : k = P.N - 1 := by omega
      subst hkN
      linarith [P.last_right]
  -- Rewrite the sum using the telescope form
  have h_eq : ∑ k : Fin P.N, P.width k = ∑ k : Fin P.N, (node (↑k + 1) - node ↑k) :=
    Finset.sum_congr rfl (fun k _ => h_width k)
  rw [h_eq]
  -- Convert Fin sum to range sum and telescope
  rw [Fin.sum_univ_eq_sum_range (fun k => node (k + 1) - node k)]
  rw [Finset.sum_range_sub (fun i => node i)]
  -- node N = a + L (since N is not < N)
  simp only [node, dif_neg (lt_irrefl P.N), dif_pos P.hN]
  -- node 0 = (bins 0).a = a
  rw [P.first_left]
  ring

/-!

### Non-Uniform Kernel

The non-uniform kernel assigns to each bin the normalized Lebesgue
measure on that bin's interval. This is exactly `binKernel (P.bins k)`
at each index `k`.
-/

/-- **Non-uniform multi-bin kernel.**

For each bin index `k : Fin N`, yields the normalized Lebesgue measure
on `[(bins k).a, (bins k).b]`:
$$\kappa_k = \frac{1}{b_k - a_k}\, \lambda\big|_{[a_k, b_k]}$$

Unlike `multiBinKernel` (which uses uniform width `1/h`), each bin uses
its own width for normalization. -/
noncomputable def nuKernel (P : Partition) : Kernel (Fin P.N) ℝ where
  toFun k := ENNReal.ofReal (1 / ((P.bins k).b - (P.bins k).a)) •
    volume.restrict (Icc (P.bins k).a (P.bins k).b)
  measurable' := measurable_of_finite _

/-- The non-uniform kernel at index `k` equals the single-bin `binKernel`. -/
theorem nuKernel_apply (P : Partition) (k : Fin P.N) :
    P.nuKernel k = binKernel (P.bins k) () := by
  show P.nuKernel.toFun k = _
  simp only [nuKernel, binKernel, Kernel.const_apply]

/-- Integration against the non-uniform kernel equals the bin average. -/
theorem nuKernel_integral (P : Partition) (f : ℝ → ℝ) (k : Fin P.N) :
    (∫ x, f x ∂(P.nuKernel k)) = binAverage f (P.bins k) := by
  rw [nuKernel_apply]
  exact binKernel_integral f (P.bins k)

/-- The Kan extension value at bin `k` equals the bin average. -/
theorem nu_lanValue_eq_binAverage (P : Partition) (f : ℝ → ℝ) (k : Fin P.N) :
    lanValue (X := ⟨ℝ, inferInstance⟩) (Y := finObj P.N)
      (fun _ => k) (measurable_const) P.nuKernel f k =
      binAverage f (P.bins k) := by
  simp only [lanValue]
  exact nuKernel_integral P f k

/-!

### Error Bounds for Non-Uniform Partitions

The per-bin midpoint error bound is immediate from `midpoint_quadrature_error`
since it depends only on `(b - a)²` for the individual bin. The composite
bound uses `hMax²` in place of `h²`.
-/

/-- **Per-bin midpoint error for non-uniform partitions.**

Each bin's midpoint approximation error is bounded by
`M₂ * width_k² / 24`, directly from `midpoint_quadrature_error`. -/
theorem nu_midpoint_error (P : Partition)
    {f : ℝ → ℝ} {M₂ : ℝ}
    (hf_bin : ∀ k : Fin P.N,
      ContDiffOn ℝ 2 f (Icc (P.bins k).a (P.bins k).b))
    (hM_bin : ∀ k : Fin P.N, ∀ x ∈ Icc (P.bins k).a (P.bins k).b,
      |iteratedDerivWithin 2 f (Icc (P.bins k).a (P.bins k).b) x| ≤ M₂)
    (k : Fin P.N) :
    |binAverage f (P.bins k) - f (P.bins k).midpoint| ≤
      M₂ * (P.width k) ^ 2 / 24 := by
  have h_err := midpoint_quadrature_error (P.bins k) (hf_bin k) (hM_bin k)
  exact h_err

/-- **Composite integral error for non-uniform partitions.**

The weighted sum `∑ width_k * (binAverage - f(midpoint))` (which
approximates the total integral error) satisfies:

$$\left|\sum_{k=0}^{N-1} h_k \cdot (\text{binAverage} - f(m_k))\right|
  \le \frac{M_2 \cdot h_{\max}^2 \cdot L}{24}$$

**Proof chain:**
```
|∑ h_k · e_k| ≤ ∑ h_k · |e_k|                    (triangle ineq)
              ≤ ∑ h_k · (M₂ · h_k² / 24)          (per-bin bound)
              = (M₂/24) · ∑ h_k³
              ≤ (M₂/24) · ∑ h_k · hMax²            (h_k² ≤ hMax²)
              = (M₂/24) · hMax² · ∑ h_k
              = (M₂/24) · hMax² · L                 (sum_widths)
              = M₂ · hMax² · L / 24
``` -/
theorem nu_composite_integral_error (P : Partition)
    {f : ℝ → ℝ} {M₂ : ℝ}
    (hM₂ : 0 ≤ M₂)
    (hf_bin : ∀ k : Fin P.N,
      ContDiffOn ℝ 2 f (Icc (P.bins k).a (P.bins k).b))
    (hM_bin : ∀ k : Fin P.N, ∀ x ∈ Icc (P.bins k).a (P.bins k).b,
      |iteratedDerivWithin 2 f (Icc (P.bins k).a (P.bins k).b) x| ≤ M₂) :
    |∑ k : Fin P.N,
      (P.width k * (binAverage f (P.bins k) - f (P.bins k).midpoint))| ≤
      M₂ * P.hMax ^ 2 * P.L / 24 := by
  -- Step 1: Triangle inequality
  calc |∑ k : Fin P.N,
        (P.width k * (binAverage f (P.bins k) - f (P.bins k).midpoint))|
      ≤ ∑ k : Fin P.N,
        |P.width k * (binAverage f (P.bins k) - f (P.bins k).midpoint)| :=
          Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k : Fin P.N,
        (P.width k * |binAverage f (P.bins k) - f (P.bins k).midpoint|) := by
          congr 1; ext k
          rw [abs_mul, abs_of_pos (P.width_pos k)]
    -- Step 2: Apply per-bin bound
    _ ≤ ∑ k : Fin P.N, (P.width k * (M₂ * (P.width k) ^ 2 / 24)) := by
          apply Finset.sum_le_sum
          intro k _
          exact mul_le_mul_of_nonneg_left (nu_midpoint_error P hf_bin hM_bin k)
            (le_of_lt (P.width_pos k))
    -- Step 3: h_k² ≤ hMax²
    _ ≤ ∑ k : Fin P.N, (P.width k * (M₂ * P.hMax ^ 2 / 24)) := by
          apply Finset.sum_le_sum
          intro k _
          apply mul_le_mul_of_nonneg_left _ (le_of_lt (P.width_pos k))
          apply div_le_div_of_nonneg_right _ (by norm_num : (0 : ℝ) < 24).le
          apply mul_le_mul_of_nonneg_left _ hM₂
          -- width k ^ 2 ≤ hMax ^ 2 from 0 ≤ width k ≤ hMax
          have hw := P.width_le_hMax k
          have hwp := le_of_lt (P.width_pos k)
          calc P.width k ^ 2 = P.width k * P.width k := sq (P.width k)
            _ ≤ P.hMax * P.hMax := mul_le_mul hw hw hwp (le_trans hwp hw)
            _ = P.hMax ^ 2 := (sq P.hMax).symm
    -- Step 4: Factor out constant and apply sum_widths
    _ = M₂ * P.hMax ^ 2 / 24 * ∑ k : Fin P.N, P.width k := by
          simp_rw [show ∀ k : Fin P.N, P.width k * (M₂ * P.hMax ^ 2 / 24) =
              (M₂ * P.hMax ^ 2 / 24) * P.width k from fun k => by ring]
          rw [← Finset.mul_sum]
    _ = M₂ * P.hMax ^ 2 / 24 * P.L := by
          rw [P.sum_widths]
    _ = M₂ * P.hMax ^ 2 * P.L / 24 := by ring

end Partition

/-!

### Uniform Partitions as Special Cases

A `UniformPartition` can be embedded into `Partition`, and its `hMax`
equals the uniform width `h`.
-/

namespace UniformPartition

/-- Embed a `UniformPartition` into the general `Partition` type. -/
noncomputable def toPartition (P : UniformPartition) : Partition where
  N := P.N
  hN := P.hN
  a := P.a
  L := P.L
  hL := P.hL
  bins := fun k => P.bin k
  adjacency := by
    intro i j hij
    simp only [bin, right, left]
    have : (↑i.val : ℝ) + 1 = (↑j.val : ℝ) := by exact_mod_cast hij
    rw [this]
  first_left := by
    simp only [bin, left]
    ring
  last_right := by
    simp only [bin, right]
    have hN' : (0 : ℝ) < ↑P.N := Nat.cast_pos.mpr P.hN
    have : (↑(P.N - 1) + 1 : ℝ) = ↑P.N := by
      rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr (Nat.pos_iff_ne_zero.mp P.hN))]
      simp
    rw [this]
    simp only [h]
    field_simp

/-- For a uniform partition, `hMax = h`: all bins have the same width. -/
theorem toPartition_hMax_eq_h (P : UniformPartition) :
    P.toPartition.hMax = P.h := by
  unfold Partition.hMax
  apply le_antisymm
  · -- hMax ≤ h: every bin has width h
    apply Finset.sup'_le
    intro k _
    show P.toPartition.width k ≤ P.h
    simp only [Partition.width, toPartition, bin, right, left]
    ring_nf; exact le_refl _
  · -- h ≤ hMax: h is one of the bin widths
    calc P.h = P.toPartition.width ⟨0, P.hN⟩ := by
            simp only [Partition.width, toPartition, bin, right, left]
            ring
      _ ≤ _ := Finset.le_sup' _ (Finset.mem_univ _)

end UniformPartition

end CpmProofs
