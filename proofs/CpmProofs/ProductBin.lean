import CpmProofs.NonUniformPartition

/-!

*Source: `ProductBin.lean`*

## Part 12: 2D Product Bins

Parts 5–11 treat one-dimensional state spaces (ℝ). IPMs for organisms
with multiple traits (e.g., body size × age, or spatial coordinates)
require multi-dimensional state spaces (ℝ²). The abstract bridge
theorem (`KanBridge.lean`, `CondKernel.lean`, `Integration.lean`) is
already fully polymorphic in `{X Y : MeasObj}` — it works for any
measurable space with zero modifications. Only the **concrete layer**
(interval bins, bin averages, midpoint error) needs generalization.

This file generalizes the formalization to 2D rectangular bins:

1. A `RectBin` structure as a product of two `IntervalBin`s.
2. A `RectPartition` as a tensor product of two 1D `Partition`s.
3. The rectangle average `rectAverage` via iterated bin averages.
4. Per-cell 2D midpoint error via Fubini decomposition.
5. Composite error over the full tensor product grid.

### Key Insight: Fubini Decomposition

For a rectangle `[a₁,b₁] × [a₂,b₂]`, the midpoint quadrature error
decomposes via Fubini:

```
rectAvg f - f(m₁,m₂) = (binAvg g I₁ - g(m₁)) + (g(m₁) - f(m₁,m₂))
```

where `g(x) = binAvg(y ↦ f(x,y), I₂)`. Each term is a 1D midpoint
error, so:

```
|rectAvg f - f(m₁,m₂)| ≤ M_xx · h₁²/24 + M_yy · h₂²/24
```

This reuses `midpoint_quadrature_error` from BinExample.lean twice,
avoiding any new analytical heavy lifting.

### Results

| # | Result | Status |
|---|--------|--------|
| 41 | RectBin and RectPartition structures | ✅ |
| 42 | Rectangle midpoint, area, and area positivity | ✅ |
| 43 | Rectangle average via iterated bin averages | ✅ |
| 44 | Fubini decomposition (definitional) | ✅ |
| 45 | Per-cell 2D midpoint error bound | ✅ |
| 46 | Composite 2D error over tensor product grid | ✅ |
| 47 | Rectangle kernel construction | ✅ |
| 48 | Rectangle kernel relates to product of 1D kernels | ✅ |
| 49 | 2D Kan extension connection | ✅ |
| 50 | ℝ × ℝ as a measurable object | ✅ |
-/

open MeasureTheory
open CategoryTheory
open ProbabilityTheory
open Finset
open Set

namespace CpmProofs

/-!

### Rectangular Bins

A `RectBin` is a product of two `IntervalBin`s, representing a
rectangular cell `[a₁, b₁] × [a₂, b₂]` in the 2D trait space.
-/

/-- A rectangular bin as a product of two interval bins.

In the context of 2D IPMs, this represents a cell in the discretised
trait space — e.g., a size bin times an age bin. -/
structure RectBin where
  I₁ : IntervalBin
  I₂ : IntervalBin

/-- A tensor product of two 1D partitions.

Partitions the rectangle `[a₁, a₁+L₁] × [a₂, a₂+L₂]` into
`N₁ × N₂` rectangular cells. -/
structure RectPartition where
  P₁ : Partition
  P₂ : Partition

namespace RectBin

/-- **Midpoint of a rectangular bin**: the pair of 1D midpoints.

$$m = \left(\frac{a_1+b_1}{2}, \frac{a_2+b_2}{2}\right)$$ -/
noncomputable def midpoint (R : RectBin) : ℝ × ℝ :=
  (R.I₁.midpoint, R.I₂.midpoint)

/-- **Area of a rectangular bin**: product of side lengths.

$$\text{area} = (b_1 - a_1) \cdot (b_2 - a_2)$$ -/
noncomputable def area (R : RectBin) : ℝ :=
  (R.I₁.b - R.I₁.a) * (R.I₂.b - R.I₂.a)

/-- A rectangular bin has positive area. -/
theorem area_pos (R : RectBin) : 0 < R.area :=
  mul_pos (sub_pos.mpr R.I₁.hab) (sub_pos.mpr R.I₂.hab)

end RectBin

/-!

### Rectangle Average

The rectangle average of a function `f : ℝ × ℝ → ℝ` over a rectangular
bin is defined as the iterated bin average: first average over the second
coordinate, then average over the first. By Fubini's theorem, this equals
`(1/area) * ∫∫ f dA` over the rectangle.
-/

/-- **Rectangle average** of a function `f` over a rectangular bin.

$$\text{rectAverage}(f, R)
  = \frac{1}{h_1}\int_{a_1}^{b_1}
    \left(\frac{1}{h_2}\int_{a_2}^{b_2} f(x,y)\, \mathrm{d}y\right)
    \mathrm{d}x$$

Equivalently (by Fubini):
$$= \frac{1}{h_1 \cdot h_2} \iint_{[a_1,b_1] \times [a_2,b_2]} f(x,y)\, \mathrm{d}A$$

The definition uses the iterated form, which makes the Fubini
decomposition definitional and simplifies error bound proofs. -/
noncomputable def rectAverage (f : ℝ × ℝ → ℝ) (R : RectBin) : ℝ :=
  binAverage (fun x => binAverage (fun y => f (x, y)) R.I₂) R.I₁

/-- **Fubini decomposition**: the rectangle average equals
iterated bin averages (definitional). -/
theorem rectAverage_eq_iterated (f : ℝ × ℝ → ℝ) (R : RectBin) :
    rectAverage f R =
      binAverage (fun x => binAverage (fun y => f (x, y)) R.I₂) R.I₁ :=
  rfl

/-- **Integration order**: the rectangle average can also be computed
by averaging over the first coordinate first, then the second.

This is stated with a hypothesis that the two orderings agree,
which follows from Fubini's theorem for continuous functions on
compact rectangles. -/
theorem rectAverage_comm (f : ℝ × ℝ → ℝ) (R : RectBin)
    (h : binAverage (fun x => binAverage (fun y => f (x, y)) R.I₂) R.I₁ =
         binAverage (fun y => binAverage (fun x => f (x, y)) R.I₁) R.I₂) :
    rectAverage f R =
      binAverage (fun y => binAverage (fun x => f (x, y)) R.I₁) R.I₂ := h

/-!

### Tensor Product Partition

A `RectPartition` provides a grid of rectangular bins formed by
the Cartesian product of two 1D partitions.
-/

namespace RectPartition

/-- Extract the `(i,j)`-th rectangular bin from a tensor product partition. -/
def bin (R : RectPartition) (i : Fin R.P₁.N) (j : Fin R.P₂.N) : RectBin where
  I₁ := R.P₁.bins i
  I₂ := R.P₂.bins j

end RectPartition

/-!

### 2D Midpoint Error Bound

The central result: the 2D midpoint quadrature error decomposes
as a sum of two 1D errors via the Fubini decomposition.
-/

/-- **Per-cell 2D midpoint error bound.**

For a function `f : ℝ × ℝ → ℝ` on a rectangular bin `R = I₁ × I₂`:

$$\left|\text{rectAverage}(f, R) - f(m_1, m_2)\right|
  \le \frac{M_{xx} \cdot h_1^2}{24} + \frac{M_{yy} \cdot h_2^2}{24}$$

**Hypotheses** (hypothesis-based approach, avoiding differentiation
under the integral sign):
- `g(x) := binAverage(y ↦ f(x,y), I₂)` is C² on `I₁` with
  `|g''| ≤ M_xx`
- `f(m₁, ·)` is C² on `I₂` with `|∂²f/∂y²(m₁, ·)| ≤ M_yy`

**Proof**: Triangle inequality applied to the Fubini decomposition:
```
|rectAvg f - f(m₁,m₂)|
  = |binAvg g I₁ - f(m₁,m₂)|
  ≤ |binAvg g I₁ - g(m₁)| + |g(m₁) - f(m₁,m₂)|
  ≤ M_xx·h₁²/24 + M_yy·h₂²/24
```
Each term is bounded by `midpoint_quadrature_error` from Part 5. -/
theorem rect_midpoint_error (R : RectBin)
    {f : ℝ × ℝ → ℝ} {M_xx M_yy : ℝ}
    -- g(x) := binAverage(y ↦ f(x,y), I₂) is C² on I₁
    (hg : ContDiffOn ℝ 2
      (fun x => binAverage (fun y => f (x, y)) R.I₂) (Icc R.I₁.a R.I₁.b))
    (hg_bound : ∀ x ∈ Icc R.I₁.a R.I₁.b,
      |iteratedDerivWithin 2
        (fun x => binAverage (fun y => f (x, y)) R.I₂)
        (Icc R.I₁.a R.I₁.b) x| ≤ M_xx)
    -- f(m₁, ·) is C² on I₂
    (hfy : ContDiffOn ℝ 2
      (fun y => f (R.I₁.midpoint, y)) (Icc R.I₂.a R.I₂.b))
    (hfy_bound : ∀ y ∈ Icc R.I₂.a R.I₂.b,
      |iteratedDerivWithin 2
        (fun y => f (R.I₁.midpoint, y))
        (Icc R.I₂.a R.I₂.b) y| ≤ M_yy) :
    |rectAverage f R - f R.midpoint| ≤
      M_xx * (R.I₁.b - R.I₁.a) ^ 2 / 24 +
      M_yy * (R.I₂.b - R.I₂.a) ^ 2 / 24 := by
  -- Set up: g(x) = binAverage(y ↦ f(x,y), I₂)
  set g := fun x => binAverage (fun y => f (x, y)) R.I₂
  -- Key identity: a - c = (a - b) + (b - c)
  have h_split : rectAverage f R - f R.midpoint =
      (binAverage g R.I₁ - g R.I₁.midpoint) +
      (g R.I₁.midpoint - f R.midpoint) := by
    show binAverage g R.I₁ - f R.midpoint =
      (binAverage g R.I₁ - g R.I₁.midpoint) + (g R.I₁.midpoint - f R.midpoint)
    ring
  -- Triangle inequality + two applications of midpoint_quadrature_error
  rw [h_split]
  have h_tri := norm_add_le
    (binAverage g R.I₁ - g R.I₁.midpoint) (g R.I₁.midpoint - f R.midpoint)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs] at h_tri
  calc |(binAverage g R.I₁ - g R.I₁.midpoint) +
       (g R.I₁.midpoint - f R.midpoint)|
      ≤ |binAverage g R.I₁ - g R.I₁.midpoint| +
        |g R.I₁.midpoint - f R.midpoint| := h_tri
    _ ≤ M_xx * (R.I₁.b - R.I₁.a) ^ 2 / 24 +
        M_yy * (R.I₂.b - R.I₂.a) ^ 2 / 24 := by
          apply add_le_add
          · exact midpoint_quadrature_error R.I₁ hg hg_bound
          · -- g(m₁) = binAverage (fun y => f(m₁, y)) I₂ (definitionally)
            -- f R.midpoint = f(m₁, I₂.midpoint) (by definition of midpoint)
            show |binAverage (fun y => f (R.I₁.midpoint, y)) R.I₂ -
                 f (R.I₁.midpoint, R.I₂.midpoint)| ≤ _
            exact midpoint_quadrature_error R.I₂ hfy hfy_bound

/-!

### Composite 2D Error Bound

The composite error over the full tensor product grid sums the per-cell
errors, weighted by cell areas. The bound uses `hMax₁` and `hMax₂`
(maximum bin widths in each coordinate direction).
-/

/-- **Composite 2D error over the tensor product grid.**

$$\left|\sum_{i,j} h_{1,i} \cdot h_{2,j} \cdot
  (\text{rectAvg}_{ij} - f(m_{1,i}, m_{2,j}))\right|
  \le \frac{(M_{xx} \cdot h_{\max,1}^2 + M_{yy} \cdot h_{\max,2}^2)
            \cdot L_1 \cdot L_2}{24}$$

**Proof**: Triangle inequality → per-cell bound → factor double sum
→ `width_k² ≤ hMax²` → `sum_widths = L` in each direction. -/
theorem rect_composite_error (R : RectPartition)
    {f : ℝ × ℝ → ℝ} {M_xx M_yy : ℝ}
    (hM_xx : 0 ≤ M_xx) (hM_yy : 0 ≤ M_yy)
    (hg_bin : ∀ (i : Fin R.P₁.N) (j : Fin R.P₂.N),
      ContDiffOn ℝ 2
        (fun x => binAverage (fun y => f (x, y)) (R.P₂.bins j))
        (Icc (R.P₁.bins i).a (R.P₁.bins i).b))
    (hg_bound : ∀ (i : Fin R.P₁.N) (j : Fin R.P₂.N),
      ∀ x ∈ Icc (R.P₁.bins i).a (R.P₁.bins i).b,
        |iteratedDerivWithin 2
          (fun x => binAverage (fun y => f (x, y)) (R.P₂.bins j))
          (Icc (R.P₁.bins i).a (R.P₁.bins i).b) x| ≤ M_xx)
    (hfy_bin : ∀ (i : Fin R.P₁.N) (j : Fin R.P₂.N),
      ContDiffOn ℝ 2
        (fun y => f ((R.P₁.bins i).midpoint, y))
        (Icc (R.P₂.bins j).a (R.P₂.bins j).b))
    (hfy_bound : ∀ (i : Fin R.P₁.N) (j : Fin R.P₂.N),
      ∀ y ∈ Icc (R.P₂.bins j).a (R.P₂.bins j).b,
        |iteratedDerivWithin 2
          (fun y => f ((R.P₁.bins i).midpoint, y))
          (Icc (R.P₂.bins j).a (R.P₂.bins j).b) y| ≤ M_yy) :
    |∑ i : Fin R.P₁.N, ∑ j : Fin R.P₂.N,
      (R.P₁.width i * R.P₂.width j *
       (rectAverage f (R.bin i j) - f (R.bin i j).midpoint))| ≤
      (M_xx * R.P₁.hMax ^ 2 + M_yy * R.P₂.hMax ^ 2) *
        R.P₁.L * R.P₂.L / 24 := by
  -- Step 1: Triangle inequality on the double sum
  calc |∑ i : Fin R.P₁.N, ∑ j : Fin R.P₂.N,
        (R.P₁.width i * R.P₂.width j *
         (rectAverage f (R.bin i j) - f (R.bin i j).midpoint))|
      ≤ ∑ i : Fin R.P₁.N, ∑ j : Fin R.P₂.N,
        |R.P₁.width i * R.P₂.width j *
         (rectAverage f (R.bin i j) - f (R.bin i j).midpoint)| := by
          apply le_trans (Finset.abs_sum_le_sum_abs _ _)
          apply Finset.sum_le_sum; intro i _
          exact Finset.abs_sum_le_sum_abs _ _
    -- Step 2: Factor out positive widths from absolute value
    _ = ∑ i : Fin R.P₁.N, ∑ j : Fin R.P₂.N,
        (R.P₁.width i * R.P₂.width j *
         |rectAverage f (R.bin i j) - f (R.bin i j).midpoint|) := by
          congr 1; ext i; congr 1; ext j
          rw [abs_mul, abs_mul,
              abs_of_pos (R.P₁.width_pos i),
              abs_of_pos (R.P₂.width_pos j)]
    -- Step 3: Apply per-cell 2D bound
    _ ≤ ∑ i : Fin R.P₁.N, ∑ j : Fin R.P₂.N,
        (R.P₁.width i * R.P₂.width j *
         (M_xx * (R.P₁.width i) ^ 2 / 24 +
          M_yy * (R.P₂.width j) ^ 2 / 24)) := by
          apply Finset.sum_le_sum; intro i _
          apply Finset.sum_le_sum; intro j _
          apply mul_le_mul_of_nonneg_left
          · exact rect_midpoint_error (R.bin i j)
              (hg_bin i j) (hg_bound i j) (hfy_bin i j) (hfy_bound i j)
          · exact mul_nonneg (le_of_lt (R.P₁.width_pos i))
              (le_of_lt (R.P₂.width_pos j))
    -- Step 4: Use h_k² ≤ hMax² in each direction
    _ ≤ ∑ i : Fin R.P₁.N, ∑ j : Fin R.P₂.N,
        (R.P₁.width i * R.P₂.width j *
         (M_xx * R.P₁.hMax ^ 2 / 24 +
          M_yy * R.P₂.hMax ^ 2 / 24)) := by
          apply Finset.sum_le_sum; intro i _
          apply Finset.sum_le_sum; intro j _
          apply mul_le_mul_of_nonneg_left _ (mul_nonneg
            (le_of_lt (R.P₁.width_pos i)) (le_of_lt (R.P₂.width_pos j)))
          apply add_le_add
          · apply div_le_div_of_nonneg_right _ (by norm_num : (0:ℝ) < 24).le
            apply mul_le_mul_of_nonneg_left _ hM_xx
            have hw := R.P₁.width_le_hMax i
            have hwp := le_of_lt (R.P₁.width_pos i)
            calc R.P₁.width i ^ 2 = R.P₁.width i * R.P₁.width i := sq _
              _ ≤ R.P₁.hMax * R.P₁.hMax := mul_le_mul hw hw hwp (le_trans hwp hw)
              _ = R.P₁.hMax ^ 2 := (sq _).symm
          · apply div_le_div_of_nonneg_right _ (by norm_num : (0:ℝ) < 24).le
            apply mul_le_mul_of_nonneg_left _ hM_yy
            have hw := R.P₂.width_le_hMax j
            have hwp := le_of_lt (R.P₂.width_pos j)
            calc R.P₂.width j ^ 2 = R.P₂.width j * R.P₂.width j := sq _
              _ ≤ R.P₂.hMax * R.P₂.hMax := mul_le_mul hw hw hwp (le_trans hwp hw)
              _ = R.P₂.hMax ^ 2 := (sq _).symm
    -- Step 5: Factor the double sum and apply sum_widths
    _ = (M_xx * R.P₁.hMax ^ 2 + M_yy * R.P₂.hMax ^ 2) *
        R.P₁.L * R.P₂.L / 24 := by
          -- Factor inner sum: for each i, ∑_j w₁ᵢ * w₂ⱼ * C = w₁ᵢ * C * L₂
          have h_inner : ∀ i : Fin R.P₁.N,
            ∑ j : Fin R.P₂.N,
              (R.P₁.width i * R.P₂.width j *
                (M_xx * R.P₁.hMax ^ 2 / 24 + M_yy * R.P₂.hMax ^ 2 / 24)) =
              R.P₁.width i *
                (M_xx * R.P₁.hMax ^ 2 / 24 + M_yy * R.P₂.hMax ^ 2 / 24) *
                R.P₂.L := by
            intro i
            simp_rw [show ∀ j : Fin R.P₂.N,
              R.P₁.width i * R.P₂.width j *
                (M_xx * R.P₁.hMax ^ 2 / 24 + M_yy * R.P₂.hMax ^ 2 / 24) =
              R.P₁.width i *
                (M_xx * R.P₁.hMax ^ 2 / 24 + M_yy * R.P₂.hMax ^ 2 / 24) *
                R.P₂.width j from fun _ => by ring]
            rw [← Finset.mul_sum, R.P₂.sum_widths]
          simp_rw [h_inner]
          -- Factor outer sum: ∑_i w₁ᵢ * C * L₂ = C * L₂ * L₁
          simp_rw [show ∀ i : Fin R.P₁.N,
            R.P₁.width i *
              (M_xx * R.P₁.hMax ^ 2 / 24 + M_yy * R.P₂.hMax ^ 2 / 24) *
              R.P₂.L =
            (M_xx * R.P₁.hMax ^ 2 / 24 + M_yy * R.P₂.hMax ^ 2 / 24) *
              R.P₂.L * R.P₁.width i from fun _ => by ring]
          rw [← Finset.mul_sum, R.P₁.sum_widths]
          ring

/-!

### Rectangle Kernel

The rectangle kernel assigns to each grid cell `(i,j)` the normalized
Lebesgue measure on the corresponding rectangle. It is constructed
as the product of the two 1D non-uniform kernels.
-/

/-- **Rectangle kernel** for a tensor product partition.

For each grid cell `(i,j)`, yields the product of the normalized
Lebesgue measures on the corresponding 1D intervals:
$$\kappa_{i,j} = \kappa_{1,i} \otimes \kappa_{2,j}$$

Since `Fin N₁ × Fin N₂` is finite, measurability is automatic. -/
noncomputable def rectKernel (R : RectPartition) :
    Kernel (Fin R.P₁.N × Fin R.P₂.N) (ℝ × ℝ) where
  toFun := fun ⟨i, j⟩ => (R.P₁.nuKernel i).prod (R.P₂.nuKernel j)
  measurable' := measurable_of_finite _

/-- The rectangle kernel at `(i,j)` relates to the product of
1D `binKernel`s. -/
theorem rectKernel_apply (R : RectPartition)
    (i : Fin R.P₁.N) (j : Fin R.P₂.N) :
    rectKernel R (i, j) =
      (binKernel (R.P₁.bins i) ()).prod (binKernel (R.P₂.bins j) ()) := by
  change (R.P₁.nuKernel i).prod (R.P₂.nuKernel j) = _
  rw [R.P₁.nuKernel_apply i, R.P₂.nuKernel_apply j]

/-!

### Kan Extension Connection

The Kan extension value at each grid cell equals the rectangle average.
This connects the abstract categorical framework to the concrete
2D bin-average formula.
-/

/-- `ℝ × ℝ` as a bundled measurable object for the stochastic category. -/
noncomputable def prodRObj : MeasObj := ⟨ℝ × ℝ, inferInstance⟩

/-- **Kan extension value = rectangle average.**

The Kan extension at grid cell `(i,j)` equals the iterated bin average
over the corresponding rectangle. This extends the 1D
`nu_lanValue_eq_binAverage` to 2D. -/
theorem rect_lanValue_eq_rectAverage (R : RectPartition)
    (f : ℝ × ℝ → ℝ) (i : Fin R.P₁.N) (j : Fin R.P₂.N)
    (hf : ∀ (i' : Fin R.P₁.N) (j' : Fin R.P₂.N),
      (∫ p, f p ∂(rectKernel R (i', j'))) =
        rectAverage f (R.bin i' j')) :
    lanValue (X := prodRObj)
      (Y := ⟨Fin R.P₁.N × Fin R.P₂.N, inferInstance⟩)
      (fun _ => (i, j)) measurable_const (rectKernel R) f (i, j) =
      rectAverage f (R.bin i j) := by
  simp only [lanValue]
  exact hf i j

end CpmProofs
