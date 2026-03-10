import CpmProofs.MarkovCat
import CpmProofs.StochSelfEnrichment

/-!

*Source: `MonoidalStoch.lean`*

## Part 20: Towards MonoidalClosed for the Stochastic Category

This module constructs the key ingredients for a `MonoidalClosed` instance
on the stochastic category, which would close the gap between the abstract
enriched Kan extension framework (Parts 10, `WeightedColimit.lean`,
`EnrichedKanExtension.lean`) and the concrete bridge theorem (Part 4).

### What this module provides

1. **Structural isomorphisms** (Results 111–114): The associator, left/right
   unitors, and braiding as categorical `Iso`s, proved via
   `Kernel.deterministic_comp_deterministic`.

2. **Fiber kernel** (Result 115): Given `κ : Kernel (X × Y) Z` and `y : Y`,
   the fiber kernel `fiberKernel κ y : Kernel X Z` maps `x ↦ κ(x, y)`.

3. **Evaluation kernel** (Result 116): The evaluation map
   `ev : Kernel (X × [X, Z]) Z` sending `(x, κ) ↦ κ(x)`. Joint
   measurability is taken as a hypothesis (holds for standard Borel spaces).

4. **Curry kernel** (Result 117): Given `κ : Kernel (X × Y) Z`, the curried
   kernel `curryKernel κ : Kernel Y [X, Z]` sends `y ↦ δ_{κ(·, y)}`.
   Measurability into the kernel-hom space is taken as a hypothesis.

5. **Eval-curry roundtrip** (Result 118): `ev ∘ (id × curry(κ)) = κ`
   (under joint measurability hypothesis).

### What remains

- **`MonoidalCategory MeasObj`**: All structural morphisms and coherence
  data are in place, but packaging into a typeclass instance requires
  `tensorHom`/`whiskerLeft` for arbitrary morphisms, which needs
  `IsSFiniteKernel` — a constraint absent from the current morphism type
  `Kernel X Y`. Resolution: restrict morphisms to s-finite (or Markov)
  kernels. This project now implements that restricted solution in
  `CpmProofs.StochMarkov`, giving a sound
  `MonoidalCategory StochMarkov`.

- **`MonoidalClosed MeasObj`**: there is a deeper obstruction than just
  naturality bookkeeping. The current `kernelHomObj X Z` packages *points*
  as kernels `X ⟶ Z`, while ordinary morphisms `Y ⟶ kernelHomObj X Z`
  in the stochastic category are themselves kernels-valued kernels,
  i.e. distributions over kernels. By contrast, `curryKernel` lands in
  deterministic kernels concentrated on the fiber kernel `x ↦ κ(x, y)`.
  Thus the present kernel-space object does not yet support a genuine
  `tensorLeft X ⊣ rightAdj` on the ordinary category of kernels; one needs
  either a restricted ambient category or a different internal-hom
  construction that accounts for non-deterministic kernel-valued morphisms.

- **Joint measurability**: The evaluation kernel `(x, κ) ↦ κ(x)(s)`
  requires joint measurability on `X × kernelHomObj X Z`. This holds for
  standard Borel spaces but is not provable for arbitrary measurable spaces.

| # | Result | Status |
|---|--------|--------|
| 111 | `assocIso` — associator isomorphism | ✅ |
| 112 | `leftUnitorIso` — left unitor isomorphism | ✅ |
| 113 | `rightUnitorIso` — right unitor isomorphism | ✅ |
| 114 | `braidingIso` — braiding isomorphism | ✅ |
| 115 | `fiberKernel` — fiber kernel κ(·, y) | ✅ |
| 116 | `evalKernel` — evaluation (x, κ) ↦ κ(x) | ✅ (joint measurability hypothesis) |
| 117 | `curryKernel` — curry of Kernel (X × Y) Z | ✅ (curry measurability hypothesis) |
| 118 | `eval_curry_roundtrip` — ev ∘ (id × curry) = κ | ✅ (uses eval hypothesis) |
-/

open CategoryTheory
open ProbabilityTheory
open MeasureTheory

universe u

namespace CpmProofs

/-!

### Structural Isomorphisms

The associator, unitors, and braiding from `MarkovCat.lean` are all
deterministic kernels. Their inverses are also deterministic. The
roundtrip compositions are proved via `Kernel.deterministic_comp_deterministic`,
reducing to the fact that the underlying functions are mutual inverses.
-/

section InverseKernels

variable (α β γ : Type u)
variable [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]

/-- Inverse of the left unitor: `x ↦ ((), x)`. -/
noncomputable def leftUnitorKernelInv : Kernel α (Unit × α) :=
  Kernel.deterministic (fun x => ((), x)) (by measurability)

/-- Inverse of the right unitor: `x ↦ (x, ())`. -/
noncomputable def rightUnitorKernelInv : Kernel α (α × Unit) :=
  Kernel.deterministic (fun x => (x, ())) (by measurability)

end InverseKernels

/-!

### Roundtrip proofs for structural isomorphisms

Each roundtrip reduces to: `deterministic(g) ∘ₖ deterministic(f)
= deterministic(g ∘ f) = deterministic(id) = Kernel.id`.
-/

section Roundtrips

variable (α β γ : Type u)
variable [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]

private theorem assoc_comp_inv :
    assocKernelInv α β γ ∘ₖ assocKernel α β γ = Kernel.id := by
  simp only [assocKernel, assocKernelInv, Kernel.id]
  rw [Kernel.deterministic_comp_deterministic]
  rfl

private theorem inv_comp_assoc :
    assocKernel α β γ ∘ₖ assocKernelInv α β γ = Kernel.id := by
  simp only [assocKernel, assocKernelInv, Kernel.id]
  rw [Kernel.deterministic_comp_deterministic]
  rfl

private theorem leftUnitor_comp_inv :
    leftUnitorKernelInv α ∘ₖ leftUnitorKernel α = Kernel.id := by
  simp only [leftUnitorKernel, leftUnitorKernelInv]
  rw [Kernel.deterministic_comp_deterministic]
  ext ⟨⟨⟩, x⟩
  simp [Kernel.deterministic_apply, Kernel.id_apply]

private theorem inv_comp_leftUnitor :
    leftUnitorKernel α ∘ₖ leftUnitorKernelInv α = Kernel.id := by
  simp only [leftUnitorKernel, leftUnitorKernelInv, Kernel.id]
  rw [Kernel.deterministic_comp_deterministic]
  rfl

private theorem rightUnitor_comp_inv :
    rightUnitorKernelInv α ∘ₖ rightUnitorKernel α = Kernel.id := by
  simp only [rightUnitorKernel, rightUnitorKernelInv]
  rw [Kernel.deterministic_comp_deterministic]
  ext ⟨x, ⟨⟩⟩
  simp [Kernel.deterministic_apply, Kernel.id_apply]

private theorem inv_comp_rightUnitor :
    rightUnitorKernel α ∘ₖ rightUnitorKernelInv α = Kernel.id := by
  simp only [rightUnitorKernel, rightUnitorKernelInv, Kernel.id]
  rw [Kernel.deterministic_comp_deterministic]
  rfl

end Roundtrips

/-!

### Categorical Isomorphisms

Package the structural kernels and their roundtrip proofs as
categorical `Iso`s in `MeasObj`.
-/

/-- **Result 111.** Associator isomorphism in the stochastic category.

`(X ⊗ Y) ⊗ Z ≅ X ⊗ (Y ⊗ Z)` via the deterministic associativity kernel.
Both directions and both roundtrips are fully proved. -/
noncomputable def assocIso (X Y Z : MeasObj) :
    (X.tensor Y).tensor Z ≅ X.tensor (Y.tensor Z) where
  hom := assocKernel X Y Z
  inv := assocKernelInv X Y Z
  hom_inv_id := assoc_comp_inv X Y Z
  inv_hom_id := inv_comp_assoc X Y Z

/-- **Result 112.** Left unitor isomorphism.

`𝟙 ⊗ X ≅ X` via projection. -/
noncomputable def leftUnitorIso (X : MeasObj) :
    MeasObj.unit.tensor X ≅ X where
  hom := leftUnitorKernel X
  inv := leftUnitorKernelInv X
  hom_inv_id := leftUnitor_comp_inv X
  inv_hom_id := inv_comp_leftUnitor X

/-- **Result 113.** Right unitor isomorphism.

`X ⊗ 𝟙 ≅ X` via projection. -/
noncomputable def rightUnitorIso (X : MeasObj) :
    X.tensor MeasObj.unit ≅ X where
  hom := rightUnitorKernel X
  inv := rightUnitorKernelInv X
  hom_inv_id := rightUnitor_comp_inv X
  inv_hom_id := inv_comp_rightUnitor X

/-- **Result 114.** Braiding isomorphism.

`X ⊗ Y ≅ Y ⊗ X` via swap. Self-inverse by `braiding_comp_braiding`. -/
noncomputable def braidingIso (X Y : MeasObj) :
    X.tensor Y ≅ Y.tensor X where
  hom := braidingKernel X Y
  inv := braidingKernel Y X
  hom_inv_id := braiding_comp_braiding X Y
  inv_hom_id := braiding_comp_braiding Y X

/-!

### Fiber Kernel

Given a kernel `κ : Kernel (X × Y) Z`, fixing the second argument gives
a family of kernels `fiberKernel κ y : Kernel X Z` for each `y : Y`.
This is the key building block for currying.
-/

/-- **Result 115.** The fiber kernel: fix the second argument of a product kernel.

Given `κ : Kernel (X × Y) Z` and `y : Y`, produces `fiberKernel κ y : Kernel X Z`
mapping `x ↦ κ(x, y)`. Measurability follows from composition with the
measurable embedding `x ↦ (x, y)`. -/
noncomputable def fiberKernel {X Y Z : MeasObj}
    (κ : Kernel (X.tensor Y) Z) (y : Y) : Kernel X Z where
  toFun x := κ (x, y)
  measurable' := κ.measurable.comp (by measurability)

@[simp]
theorem fiberKernel_apply {X Y Z : MeasObj}
    (κ : Kernel (X.tensor Y) Z) (y : Y) (x : X) :
    fiberKernel κ y x = κ (x, y) := rfl

/-!

### Evaluation Kernel

The evaluation kernel `evalKernel : Kernel (X × [X, Z]) Z` maps `(x, κ) ↦ κ(x)`.
This is the counit of the tensor-hom adjunction.

**Joint measurability**: The map `(x, κ) ↦ κ(x)(s)` must be measurable on
`X × kernelHomObj X Z` for every measurable `s`. This holds for standard
Borel spaces (where the kernel space has a compatible Borel structure) but
is not provable for arbitrary measurable spaces. We take it as a hypothesis.
-/

/-- **Result 116.** The evaluation kernel: `(x, κ) ↦ κ(x)`.

This is the counit of the would-be tensor-hom adjunction for `MonoidalClosed`.
The underlying function sends a pair `(x, κ)` — a point and a kernel —
to the measure `κ(x)` on `Z`.

**Measurability status**: Joint measurability of `(x, κ) ↦ κ(x)(s)` on
`X × kernelHomObj X Z` is taken as a hypothesis. It holds when `X` and `Z`
are standard Borel spaces (the kernel space inherits a standard Borel
structure from the pointwise sigma-algebra). For general measurable spaces,
this is a nontrivial measure-theoretic result.

The `measurable_kernel_eval` lemma from `StochSelfEnrichment.lean` proves
measurability in `κ` for *fixed* `x`. The remaining gap is *joint*
measurability in both arguments simultaneously. -/
noncomputable def evalKernel (X Z : MeasObj)
    (h_joint : Measurable (fun p : (X.tensor (kernelHomObj X Z)) =>
      ((show Kernel X Z from p.2) : X → Measure Z) p.1)) :
    Kernel (X.tensor (kernelHomObj X Z)) Z where
  toFun p := (show Kernel X Z from p.2) p.1
  measurable' := h_joint

@[simp]
theorem evalKernel_apply (X Z : MeasObj) (h_joint) (x : X) (κ : kernelHomObj X Z) :
    evalKernel X Z h_joint (x, κ) = (show Kernel X Z from κ) x := rfl

/-!

### Curry Kernel

Given `κ : Kernel (X × Y) Z`, the curried kernel `curryKernel κ : Kernel Y [X, Z]`
sends `y ↦ δ_{fiberKernel κ y}` — the Dirac mass on the kernel `x ↦ κ(x, y)`.

This is a **deterministic** kernel: for each `y`, the "distribution over
kernels" is concentrated on a single kernel. This is the simplest case of
currying — the general case (where the curried version is a genuine
distribution over kernels) would require kernel-valued disintegration.

**Measurability**: The map `y ↦ fiberKernel κ y` must be measurable into
`kernelHomObj X Z` (which has a comap sigma-algebra from the pointwise
structure). This requires: for each `x : X` and measurable `s : Set Z`,
`y ↦ κ(x, y)(s)` is measurable — which holds by measurability of `κ`
composed with the measurable map `y ↦ (x, y)`. The formal proof requires
careful navigation of the comap sigma-algebra, so we take this as a
hypothesis.
-/

/-- **Result 117.** The curry kernel: `Kernel (X × Y) Z → Kernel Y [X, Z]`.

Given a kernel `κ` on the product, produces a deterministic kernel sending
`y` to the Dirac mass on the fiber kernel `fiberKernel κ y : Kernel X Z`.

This is the unit direction of the tensor-hom adjunction: it converts a
kernel on a product into a kernel-valued function. The currying is
deterministic (Dirac) because we fix the second argument rather than
integrating it out.

**Measurability**: Taken as a hypothesis. The underlying mathematical
fact is: for each `x : X` and measurable `s : Set Z`, the map
`y ↦ κ(x, y)(s)` is measurable (by measurability of `κ` composed with
`y ↦ (x, y)`). Packaging this into measurability into the comap
sigma-algebra on `kernelHomObj X Z` is the remaining formal step. -/
noncomputable def curryKernel {X Y Z : MeasObj}
    (κ : Kernel (X.tensor Y) Z)
    (h_curry : @Measurable Y (kernelHomObj X Z) _ (kernelHomObj X Z).inst
      (fun y => (fiberKernel κ y : Kernel X Z))) :
    Kernel Y (kernelHomObj X Z) :=
  Kernel.deterministic
    (fun y => (fiberKernel κ y : Kernel X Z))
    h_curry

@[simp]
theorem curryKernel_eq_deterministic {X Y Z : MeasObj}
    (κ : Kernel (X.tensor Y) Z)
    (h_curry : @Measurable Y (kernelHomObj X Z) _ (kernelHomObj X Z).inst
      (fun y => (fiberKernel κ y : Kernel X Z))) :
    curryKernel κ h_curry =
      Kernel.deterministic (fun y => (fiberKernel κ y : kernelHomObj X Z)) h_curry :=
  rfl

/-!

### Eval-Curry Roundtrip

The fundamental identity of the tensor-hom adjunction:
evaluating a curried kernel recovers the original kernel.

`evalKernel ∘ (id × curryKernel κ) = κ`

More precisely: for all `(x, y) : X × Y`,
`evalKernel(x, fiberKernel κ y) = κ(x, y)`.
-/

/-- **Result 118.** The eval-curry roundtrip identity.

For any kernel `κ : Kernel (X × Y) Z` and points `x : X`, `y : Y`:

`evalKernel(x, curryKernel(κ)(y)) = κ(x, y)`

This is the counit-unit identity for the would-be tensor-hom adjunction.
The proof is straightforward: `curryKernel(κ)(y)` is the Dirac mass on
`fiberKernel κ y`, so evaluating at `x` gives `(fiberKernel κ y)(x) = κ(x, y)`.

Note: This theorem is stated pointwise (for a fixed `y` drawn from the
Dirac mass) rather than as a kernel composition, to avoid the need for
`IsSFiniteKernel` on the intermediate kernel. -/
theorem eval_curry_roundtrip {X Y Z : MeasObj}
    (κ : Kernel (X.tensor Y) Z) (h_joint)
    (x : X) (y : Y) :
    evalKernel X Z h_joint (x, fiberKernel κ y) = κ (x, y) := by
  simp [evalKernel_apply, fiberKernel_apply]

/-!

### Discussion: Path to MonoidalClosed

The constructions above provide the key data for a `MonoidalClosed MeasObj`
instance. The remaining steps are:

#### Step 1: MonoidalCategory MeasObj

The structural isomorphisms (Results 111–114) provide the `associator`,
`leftUnitor`, `rightUnitor`, and `braiding`. The tensor product of objects
is `MeasObj.tensor`. The tensor product of *morphisms* requires
`Kernel.parallelComp`, which assumes `IsSFiniteKernel`.

**Resolution**: Restrict the morphism type to s-finite kernels:
`Hom X Y = { κ : Kernel X Y // IsSFiniteKernel κ }`.
In this project we take the sharper Markov-kernel version
`CpmProofs.StochMarkov`, whose morphisms are Markov kernels and
therefore automatically finite and s-finite. All kernels arising from the
bridge theorem (conditional kernels, deterministic embeddings, identity)
lie in that restricted setting.

The coherence axioms (pentagon, triangle, naturality of associator/unitors)
reduce to function equality for deterministic kernels via
`Kernel.deterministic_comp_deterministic`.

#### Step 2: MonoidalClosed MeasObj

- **Internal hom**: `kernelHomObj X Z` from `StochSelfEnrichment.lean`.
- **Evaluation**: `evalKernel X Z` (Result 116), modulo joint measurability.
- **Curry**: `curryKernel` (Result 117), modulo curry measurability.
- **Adjunction**: The eval-curry roundtrip (Result 118) gives one triangle
  identity for kernels on products. However, `curryKernel` is visibly
  deterministic (`curryKernel_eq_deterministic`), whereas ordinary morphisms into the
  kernel-space object are general kernels-valued kernels. So the missing
  issue is not merely a proof gap: a genuine `Closed` instance on the
  current ordinary category would require a different account of the
  codomain of currying, or a restriction of the ambient morphisms.

#### Step 3: Joint measurability

The evaluation kernel requires `(x, κ) ↦ κ(x)(s)` to be jointly measurable
on `X × kernelHomObj X Z`. This holds for **standard Borel spaces**
(countably generated, separable metrizable) — the kernel space inherits
a standard Borel structure. For the IPM application, all relevant spaces
(real intervals, finite sets) are standard Borel.

#### Step 4: Bridge as enriched identity

Once `MonoidalClosed MeasObj` is available:
- `StochSelfEnrichment.lean`'s abstract section gives `EnrichedOrdinaryCategory`.
- `WeightedColimit.lean` + `EnrichedKanExtension.lean` provide the enriched
  Kan extension formula.
- `KanBridge.lean`'s `IsStochKanExtension` becomes an instance of
  `IsPointwiseEnrichedLeftKanExtensionAt`.
-/

end CpmProofs
