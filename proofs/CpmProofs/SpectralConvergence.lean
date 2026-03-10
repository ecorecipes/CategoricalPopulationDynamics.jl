import CpmProofs.MultiBin
import Mathlib.Data.Matrix.Basic

/-!

*Source: `SpectralConvergence.lean`*

## Part 17: Spectral convergence reduction

The quadrature files already control midpoint discretisation error at the level of
individual bin averages. For IPM matrices, the relevant entries are weighted by the
bin width `h`, so each matrix entry has `O(h³)` midpoint error and each row has
total absolute error `O(h²)`.

This file packages that observation at the matrix level. It does not yet prove the
missing spectral perturbation theorem for the dominant eigenvalue itself; instead, it
shows that any candidate dominant-eigenvalue functional controlled by the row-sum
distance automatically inherits the `O(h²)` midpoint convergence rate from the
existing quadrature formalisation.

| # | Result | Status |
|---|--------|--------|
| 91 | Exact and midpoint discretisation rows | ✅ |
| 92 | `discretizationRow_entry_error` | ✅ |
| 93 | `discretizationRow_l1_error` | ✅ |
| 94 | `rowSumNormDist_midpoint_le` | ✅ |
| 95 | `dominantEigenvalue_error_of_rowSumNorm_control` | ✅ |
-/

open Finset

namespace CpmProofs

/-- The exact discretised row obtained by integrating over each bin. -/
noncomputable def exactDiscretizationRow (P : UniformPartition) (f : ℝ → ℝ) : Fin P.N → ℝ :=
  fun j => P.h * binAverage f (P.bin j)

/-- The midpoint discretised row obtained by evaluating at each bin midpoint. -/
noncomputable def midpointDiscretizationRow (P : UniformPartition) (f : ℝ → ℝ) :
    Fin P.N → ℝ :=
  fun j => P.h * f (P.bin j).midpoint

/-- Each weighted matrix entry has `O(h³)` midpoint error. -/
theorem discretizationRow_entry_error (P : UniformPartition)
    {f : ℝ → ℝ} {M₂ : ℝ}
    (hf_bin : ∀ k : Fin P.N,
      ContDiffOn ℝ 2 f (Set.Icc (P.bin k).a (P.bin k).b))
    (hM_bin : ∀ k : Fin P.N, ∀ x ∈ Set.Icc (P.bin k).a (P.bin k).b,
      |iteratedDerivWithin 2 f (Set.Icc (P.bin k).a (P.bin k).b) x| ≤ M₂)
    (j : Fin P.N) :
    |exactDiscretizationRow P f j - midpointDiscretizationRow P f j| ≤
      M₂ * P.h ^ 3 / 24 := by
  have h_entry := multiBinKanVector_midpoint_error P hf_bin hM_bin j
  dsimp [exactDiscretizationRow, midpointDiscretizationRow]
  rw [show P.h * binAverage f (P.bin j) - P.h * (f (P.bin j).midpoint) =
      P.h * (binAverage f (P.bin j) - f (P.bin j).midpoint) by ring]
  rw [abs_mul, abs_of_pos P.h_pos]
  calc
    P.h * |binAverage f (P.bin j) - f (P.bin j).midpoint|
      ≤ P.h * (M₂ * P.h ^ 2 / 24) := by
        exact mul_le_mul_of_nonneg_left h_entry (le_of_lt P.h_pos)
    _ = M₂ * P.h ^ 3 / 24 := by ring

/-- Summing the weighted entrywise errors over one row gives the expected `O(h²)` bound. -/
theorem discretizationRow_l1_error (P : UniformPartition)
    {f : ℝ → ℝ} {M₂ : ℝ}
    (hf_bin : ∀ k : Fin P.N,
      ContDiffOn ℝ 2 f (Set.Icc (P.bin k).a (P.bin k).b))
    (hM_bin : ∀ k : Fin P.N, ∀ x ∈ Set.Icc (P.bin k).a (P.bin k).b,
      |iteratedDerivWithin 2 f (Set.Icc (P.bin k).a (P.bin k).b) x| ≤ M₂) :
    ∑ j : Fin P.N, |exactDiscretizationRow P f j - midpointDiscretizationRow P f j| ≤
      M₂ * P.L * P.h ^ 2 / 24 := by
  calc
    ∑ j : Fin P.N, |exactDiscretizationRow P f j - midpointDiscretizationRow P f j|
      ≤ ∑ j : Fin P.N, M₂ * P.h ^ 3 / 24 := by
          exact Finset.sum_le_sum (fun j _ => discretizationRow_entry_error P hf_bin hM_bin j)
    _ = (P.N : ℝ) * (M₂ * P.h ^ 3 / 24) := by simp
    _ = M₂ * ((P.N : ℝ) * P.h) * P.h ^ 2 / 24 := by ring
    _ = M₂ * P.L * P.h ^ 2 / 24 := by
        unfold UniformPartition.h
        have hN' : (P.N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt P.hN)
        field_simp

/-- The exact matrix whose `(i,j)` entry is the exact bin integral in row `i`, column `j`. -/
noncomputable def exactDiscretizationMatrix (P : UniformPartition)
    (K : Fin P.N → ℝ → ℝ) : Matrix (Fin P.N) (Fin P.N) ℝ :=
  fun i j => exactDiscretizationRow P (K i) j

/-- The midpoint matrix whose `(i,j)` entry is `h * K_i(m_j)`. -/
noncomputable def midpointDiscretizationMatrix (P : UniformPartition)
    (K : Fin P.N → ℝ → ℝ) : Matrix (Fin P.N) (Fin P.N) ℝ :=
  fun i j => midpointDiscretizationRow P (K i) j

/-- Row-sum distance, i.e. the maximum over rows of the sum of absolute entrywise differences. -/
noncomputable def rowSumNormDist (P : UniformPartition)
    (A B : Matrix (Fin P.N) (Fin P.N) ℝ) : ℝ :=
  Finset.sup' Finset.univ ⟨⟨0, P.hN⟩, Finset.mem_univ _⟩ (fun i => ∑ j, |A i j - B i j|)

/-- The exact and midpoint matrices are `O(h²)` apart in row-sum distance. -/
theorem rowSumNormDist_midpoint_le (P : UniformPartition)
    {K : Fin P.N → ℝ → ℝ} {M₂ : ℝ}
    (hf_bin : ∀ i : Fin P.N, ∀ k : Fin P.N,
      ContDiffOn ℝ 2 (K i) (Set.Icc (P.bin k).a (P.bin k).b))
    (hM_bin : ∀ i : Fin P.N, ∀ k : Fin P.N, ∀ x ∈ Set.Icc (P.bin k).a (P.bin k).b,
      |iteratedDerivWithin 2 (K i) (Set.Icc (P.bin k).a (P.bin k).b) x| ≤ M₂) :
    rowSumNormDist P (exactDiscretizationMatrix P K) (midpointDiscretizationMatrix P K)
      ≤ M₂ * P.L * P.h ^ 2 / 24 := by
  unfold rowSumNormDist
  exact Finset.sup'_le (s := Finset.univ)
    (H := ⟨⟨0, P.hN⟩, Finset.mem_univ _⟩)
    (f := fun i : Fin P.N =>
      ∑ j, |exactDiscretizationMatrix P K i j - midpointDiscretizationMatrix P K i j|)
    (a := M₂ * P.L * P.h ^ 2 / 24)
    (fun i _hi => by
      simpa [exactDiscretizationMatrix, midpointDiscretizationMatrix] using
        discretizationRow_l1_error P (hf_bin i) (hM_bin i))

/-- Any dominant-eigenvalue functional controlled by row-sum distance inherits the
same `O(h²)` midpoint discretisation error bound. -/
theorem dominantEigenvalue_error_of_rowSumNorm_control (P : UniformPartition)
    {K : Fin P.N → ℝ → ℝ} {M₂ : ℝ}
    (dominantEigenvalue : Matrix (Fin P.N) (Fin P.N) ℝ → ℝ)
    (hLip : ∀ A B : Matrix (Fin P.N) (Fin P.N) ℝ,
      |dominantEigenvalue A - dominantEigenvalue B| ≤ rowSumNormDist P A B)
    (hf_bin : ∀ i : Fin P.N, ∀ k : Fin P.N,
      ContDiffOn ℝ 2 (K i) (Set.Icc (P.bin k).a (P.bin k).b))
    (hM_bin : ∀ i : Fin P.N, ∀ k : Fin P.N, ∀ x ∈ Set.Icc (P.bin k).a (P.bin k).b,
      |iteratedDerivWithin 2 (K i) (Set.Icc (P.bin k).a (P.bin k).b) x| ≤ M₂) :
    |dominantEigenvalue (exactDiscretizationMatrix P K) -
        dominantEigenvalue (midpointDiscretizationMatrix P K)| ≤
      M₂ * P.L * P.h ^ 2 / 24 := by
  calc
    |dominantEigenvalue (exactDiscretizationMatrix P K) -
        dominantEigenvalue (midpointDiscretizationMatrix P K)|
      ≤ rowSumNormDist P (exactDiscretizationMatrix P K) (midpointDiscretizationMatrix P K) :=
        hLip _ _
    _ ≤ M₂ * P.L * P.h ^ 2 / 24 := rowSumNormDist_midpoint_le P hf_bin hM_bin

end CpmProofs
