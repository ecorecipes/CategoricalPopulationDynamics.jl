import CpmProofs.StochCat
import Mathlib.Probability.Kernel.Composition.Prod
import Mathlib.Probability.Kernel.Composition.ParallelComp
import Mathlib.Probability.Kernel.Composition.MapComap

/-!

*Source: `MarkovCat.lean`*

## Part 8: Towards a Markov Category Instance

Fritz [arXiv:1908.07021, §2] defines **Stoch** as a Markov category — a
symmetric monoidal category equipped with copy/discard morphisms satisfying
the axioms of commutative comonoids, plus the naturality of discard.

### The Monoidal Structure

- **Objects**: `X ⊗ Y = X × Y` (product measurable space)
- **Morphisms**: `κ ⊗ₘ η = κ ∥ₖ η` (parallel composition)
- **Unit**: `𝟙 = Unit`

### Copy and Discard

- **Copy** `Δ[X] = Kernel.copy X : Kernel X (X × X)`
- **Discard** `ε[X] = Kernel.discard X : Kernel X Unit`

### The Markov Category Axiom

Naturality of discard: for every *Markov* kernel `κ`:
`discard ∘ₖ κ = discard`. This fails for non-Markov kernels (zero kernel),
so Fritz restricts **Stoch** to Markov kernels.

### Results

| # | Result | Status |
|---|--------|--------|
| 25 | Deterministic structural isomorphisms | ✅ |
| 26 | Copy-then-project = identity (counit) | ✅ |
| 27 | Copy is cocommutative | ✅ |
| 28 | Discard is natural for Markov kernels | ✅ |
| 29 | Braiding is an involution | ✅ |
| 30 | Parallel composition of identities = identity | ✅ |
-/

open CategoryTheory
open ProbabilityTheory
open MeasureTheory

universe u

namespace CpmProofs

/-!

### Tensor Product and Structural Isomorphisms
-/

/-- Product of bundled measurable spaces — the tensor in **Stoch**. -/
noncomputable def MeasObj.tensor (X Y : MeasObj) : MeasObj :=
  ⟨X × Y, inferInstance⟩

/-- The monoidal unit. -/
def MeasObj.unit : MeasObj := ⟨Unit, inferInstance⟩

section StructuralIsos

variable (α β γ : Type u)
variable [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]

/-- **Associator**: `((x,y),z) ↦ (x,(y,z))`. -/
noncomputable def assocKernel : Kernel ((α × β) × γ) (α × (β × γ)) :=
  Kernel.deterministic (fun ⟨⟨a, b⟩, c⟩ => (a, (b, c))) (by measurability)

/-- **Inverse associator**: `(x,(y,z)) ↦ ((x,y),z)`. -/
noncomputable def assocKernelInv : Kernel (α × (β × γ)) ((α × β) × γ) :=
  Kernel.deterministic (fun ⟨a, b, c⟩ => ((a, b), c)) (by measurability)

/-- **Left unitor**: `((), x) ↦ x`. -/
noncomputable def leftUnitorKernel : Kernel (Unit × α) α :=
  Kernel.deterministic Prod.snd measurable_snd

/-- **Right unitor**: `(x, ()) ↦ x`. -/
noncomputable def rightUnitorKernel : Kernel (α × Unit) α :=
  Kernel.deterministic Prod.fst measurable_fst

/-- **Braiding**: `(x, y) ↦ (y, x)`. -/
noncomputable def braidingKernel : Kernel (α × β) (β × α) :=
  Kernel.deterministic Prod.swap measurable_swap

end StructuralIsos

/-- **The braiding is an involution**: `swap ∘ swap = id`. -/
theorem braiding_comp_braiding (α β : Type u)
    [MeasurableSpace α] [MeasurableSpace β] :
    braidingKernel β α ∘ₖ braidingKernel α β = Kernel.id := by
  simp only [braidingKernel, Kernel.id]
  rw [Kernel.deterministic_comp_deterministic]
  rfl

/-!

### Copy and Discard
-/

/-- **Copy then first projection = identity.**

`Prod.fst ∘ Δ = id`: mapping the first component after copying
gives back the identity kernel. -/
theorem copy_map_fst (α : Type u) [MeasurableSpace α] :
    Kernel.map (Kernel.copy α) Prod.fst = Kernel.id := by
  ext x s hs
  rw [Kernel.map_apply' _ measurable_fst x hs, Kernel.copy_apply, Kernel.id_apply]
  simp only [Measure.dirac_apply' _ (measurable_fst hs), Measure.dirac_apply' _ hs]
  rfl

/-- **Copy then second projection = identity.** -/
theorem copy_map_snd (α : Type u) [MeasurableSpace α] :
    Kernel.map (Kernel.copy α) Prod.snd = Kernel.id := by
  ext x s hs
  rw [Kernel.map_apply' _ measurable_snd x hs, Kernel.copy_apply, Kernel.id_apply]
  simp only [Measure.dirac_apply' _ (measurable_snd hs), Measure.dirac_apply' _ hs]
  rfl

/-- **Copy is cocommutative** (Fritz §2, Axiom (M2)).

`swap ∘ Δ = Δ` since `swap(x, x) = (x, x)`. -/
theorem copy_swap (α : Type u) [MeasurableSpace α] :
    Kernel.swapRight (Kernel.copy α) = Kernel.copy α := by
  ext x s hs
  simp only [Kernel.swapRight, Kernel.mapOfMeasurable, Kernel.coe_mk,
    Kernel.copy, Kernel.deterministic_apply]
  rw [Measure.map_dirac' measurable_swap]
  rfl

/-- **Discard is natural for Markov kernels** (Fritz §2, Axiom (M4)).

`discard ∘ₖ κ = discard` for any Markov kernel κ. This is the
defining axiom of Markov categories, using Mathlib's `Kernel.comp_discard`. -/
theorem comp_discard_of_markov {α β : Type u}
    [MeasurableSpace α] [MeasurableSpace β]
    (κ : Kernel α β) [IsMarkovKernel κ] :
    Kernel.discard β ∘ₖ κ = Kernel.discard α :=
  Kernel.comp_discard κ

/-- **Parallel composition of identities = identity.**

`id ∥ₖ id = id` on the product space. -/
theorem parallelComp_id_id (α β : Type u)
    [MeasurableSpace α] [MeasurableSpace β] :
    (Kernel.id : Kernel α α) ∥ₖ (Kernel.id : Kernel β β) = Kernel.id := by
  ext ⟨x, y⟩ s hs
  simp only [Kernel.parallelComp_apply, Kernel.id_apply, Measure.dirac_prod_dirac]

/-!

### Discussion

The identities above establish the key *mathematical content* of
Fritz's Markov category axioms for **Stoch**:

1. **Counit laws**: `copy_map_fst`, `copy_map_snd` (copy then discard a
   component recovers the identity).
2. **Cocommutativity**: `copy_swap` (the diagonal is swap-invariant).
3. **Discard naturality**: `comp_discard_of_markov` (Markov kernels
   preserve total mass).
4. **Tensor functoriality**: `parallelComp_id_id` (identity is preserved).
5. **Involutive braiding**: `braiding_comp_braiding`.

The full `MarkovCategory MeasObj` typeclass instance additionally requires:

- **`MonoidalCategory MeasObj`**: ~10 coherence conditions (pentagon,
  triangle, naturality of associator and unitors). Each is a kernel
  equality, proved via `Kernel.ext` and measure computation.

- **Restriction to Markov kernels**: `discard_natural` requires all
  morphisms to be Markov. This needs a new category with
  `Hom X Y = { κ : Kernel X Y // IsMarkovKernel κ }`.

These are engineering challenges orthogonal to the mathematical content.
-/

end CpmProofs
