import CpmProofs.CompositeError

/-!

*Source: `MultiBin.lean`*

## Part 7: Multi-Bin Extension

Part 5 treated a single interval bin `[a, b]` with the trivial coarsening
`D : ℝ → Unit`. In practice, IPMs partition the domain into `N` bins and
compute a kernel *matrix*. This file extends the formalization to `N` bins
using `Fin N` as the target space.

### Setup

- **State space**: `ℝ` (continuous trait values)
- **Bin space**: `Fin N` (discrete bin indices)
- **Conditional kernel**: At bin `k`, the normalized Lebesgue measure
  on `[a_k, b_k]`

### Results

| # | Result | Status |
|---|--------|--------|
| 21 | Multi-bin kernel construction | ✅ |
| 22 | Multi-bin kernel integral = bin average | ✅ |
| 23 | Multi-bin Kan extension = bin averages | ✅ |
| 24 | Midpoint approximation for all bins | ✅ |
-/

open CategoryTheory
open ProbabilityTheory
open MeasureTheory
open Set

universe u

namespace CpmProofs

/-!

### Fin N as a Measurable Space

`Fin N` carries the discrete (⊤) σ-algebra from Mathlib, making every
subset measurable and every function *into* `Fin N` measurable when the
preimages of singletons are measurable.
-/

/-- `Fin N` as a bundled measurable object for the stochastic category. -/
def finObj (N : ℕ) : MeasObj := ⟨Fin N, inferInstance⟩

/-!

### The Multi-Bin Kernel

The multi-bin kernel `multiBinKernel P : Kernel (Fin N) ℝ` assigns to each
bin index `k` the normalized Lebesgue measure on the `k`-th subinterval.
This extends `binKernel` from Part 5 to multiple bins.
-/

/-- **Multi-bin conditional kernel.**

For each bin index `k : Fin N`, the kernel yields the normalized Lebesgue
measure on `[a_k, b_k]`:
$$\kappa_k = \frac{1}{h}\, \text{volume.restrict}\ [a_k, b_k]$$

Since `Fin N` is finite, the measurability of the kernel (as a function
from `Fin N` to `Measure ℝ`) is automatic. -/
noncomputable def multiBinKernel (P : UniformPartition) : Kernel (Fin P.N) ℝ where
  toFun k := ENNReal.ofReal (1 / P.h) • volume.restrict (Icc (P.bin k).a (P.bin k).b)
  measurable' := measurable_of_finite _

/-- The multi-bin kernel at index `k` equals the single-bin `binKernel`. -/
theorem multiBinKernel_apply (P : UniformPartition) (k : Fin P.N) :
    multiBinKernel P k = binKernel (P.bin k) () := by
  show (multiBinKernel P).toFun k = _
  simp only [multiBinKernel, binKernel, Kernel.const_apply]
  congr 1
  rw [P.bin_width]

/-!

### Integration Against the Multi-Bin Kernel
-/

/-- **Integration against the multi-bin kernel equals the bin average.**

For each bin index `k : Fin N`:
$$\int f\, \mathrm{d}(\kappa_k) = \text{binAverage}(f, I_k)$$ -/
theorem multiBinKernel_integral (P : UniformPartition) (f : ℝ → ℝ) (k : Fin P.N) :
    (∫ x, f x ∂(multiBinKernel P k)) = binAverage f (P.bin k) := by
  rw [multiBinKernel_apply]
  exact binKernel_integral f (P.bin k)

/-!

### Multi-Bin Kan Extension Values
-/

/-- **Multi-bin Kan extension values.**

The Kan extension value at each bin index `k` gives the bin average of `f`
over that bin. This extends `lanValue_eq_binAverage` from Part 5.

In the context of IPMs, this says: the `(i,j)` entry of the discretised
kernel matrix (before the `h` factor) is `binAverage(K(z_i, ·), I_j)`,
which is precisely the Kan extension value. -/
theorem multiBin_lanValue_eq_binAverage (P : UniformPartition) (f : ℝ → ℝ) (k : Fin P.N) :
    lanValue (X := ⟨ℝ, inferInstance⟩) (Y := finObj P.N)
      (fun _ => k) (measurable_const) (multiBinKernel P) f k =
      binAverage f (P.bin k) := by
  simp only [lanValue]
  exact multiBinKernel_integral P f k

/-- **Midpoint approximation for multi-bin Kan extension.**

At each bin, the midpoint value `f(midpoint_k)` approximates the Kan
extension value to `O(h²)`, extending `midpoint_approximates_lanValue`
from Part 5:

$$\left|(\text{Lan}\, f)(k) - f(m_k)\right| \le \frac{M_2 \cdot h^2}{24}$$

This is the formal justification for midpoint quadrature in IPM kernel
discretisation: each matrix entry has error bounded by `M₂ · h² / 24`. -/
theorem multiBin_midpoint_approximates (P : UniformPartition)
    {f : ℝ → ℝ} {M₂ : ℝ}
    (hf_bin : ∀ k : Fin P.N,
      ContDiffOn ℝ 2 f (Icc (P.bin k).a (P.bin k).b))
    (hM_bin : ∀ k : Fin P.N, ∀ x ∈ Icc (P.bin k).a (P.bin k).b,
      |iteratedDerivWithin 2 f (Icc (P.bin k).a (P.bin k).b) x| ≤ M₂)
    (k : Fin P.N) :
    |binAverage f (P.bin k) - f (P.bin k).midpoint| ≤
      M₂ * P.h ^ 2 / 24 := by
  have h_err := midpoint_quadrature_error (P.bin k) (hf_bin k) (hM_bin k)
  rwa [P.bin_width k] at h_err

/-- **The vector of Kan extension values.**

Collects all bin averages into a function `Fin N → ℝ`, representing
a row of the IPM kernel matrix (before the `h` factor). -/
noncomputable def multiBinKanVector (P : UniformPartition) (f : ℝ → ℝ) : Fin P.N → ℝ :=
  fun k => binAverage f (P.bin k)

/-- **Midpoint vector approximation.**

The midpoint vector `k ↦ f(midpoint_k)` approximates the Kan vector
entrywise to `O(h²)`. This is the matrix-level error bound for IPM
discretisation. -/
theorem multiBinKanVector_midpoint_error (P : UniformPartition)
    {f : ℝ → ℝ} {M₂ : ℝ}
    (hf_bin : ∀ k : Fin P.N,
      ContDiffOn ℝ 2 f (Icc (P.bin k).a (P.bin k).b))
    (hM_bin : ∀ k : Fin P.N, ∀ x ∈ Icc (P.bin k).a (P.bin k).b,
      |iteratedDerivWithin 2 f (Icc (P.bin k).a (P.bin k).b) x| ≤ M₂) :
    ∀ k : Fin P.N,
      |multiBinKanVector P f k - f (P.bin k).midpoint| ≤ M₂ * P.h ^ 2 / 24 :=
  multiBin_midpoint_approximates P hf_bin hM_bin

end CpmProofs
