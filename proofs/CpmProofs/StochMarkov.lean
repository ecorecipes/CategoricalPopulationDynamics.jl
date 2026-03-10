import CpmProofs.MarkovCat
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.Probability.Kernel.Composition.KernelLemmas

/-!

*Source: `StochMarkov.lean`*

## Part 21: A sound monoidal category of Markov kernels

`MonoidalStoch.lean` explains why `MeasObj` itself cannot carry the intended
tensor on all kernels: `Kernel.parallelComp` is only mathematically sound once
the morphisms are restricted to a regime such as Markov or s-finite kernels.

This module packages the clean restricted ambient category:

* objects: measurable spaces
* morphisms: Markov kernels
* tensor on objects: measurable products
* tensor on morphisms: `Kernel.parallelComp`
* tensor unit: `PUnit`

The `PUnit` tensor unit avoids the universe issues that appeared with `Unit` in
the coherence proofs. Markov kernels are automatically finite, hence s-finite,
so the tensor-on-morphisms identities can use Mathlib's `parallelComp` API
without any junk-value fallback.
-/

noncomputable section

open CategoryTheory
open ProbabilityTheory
open MeasureTheory
open scoped MonoidalCategory

universe u

namespace CpmProofs

section KernelLevel

variable {X₁ X₂ X₃ Y₁ Y₂ Y₃ : Type u}
variable [MeasurableSpace X₁] [MeasurableSpace X₂] [MeasurableSpace X₃]
variable [MeasurableSpace Y₁] [MeasurableSpace Y₂] [MeasurableSpace Y₃]

noncomputable def punitLeftUnitorKernel (α : Type u) [MeasurableSpace α] :
    Kernel (PUnit × α) α :=
  Kernel.deterministic Prod.snd measurable_snd

noncomputable def punitLeftUnitorKernelInv (α : Type u) [MeasurableSpace α] :
    Kernel α (PUnit × α) :=
  Kernel.deterministic (fun x => (PUnit.unit, x)) (by measurability)

noncomputable def punitRightUnitorKernel (α : Type u) [MeasurableSpace α] :
    Kernel (α × PUnit) α :=
  Kernel.deterministic Prod.fst measurable_fst

noncomputable def punitRightUnitorKernelInv (α : Type u) [MeasurableSpace α] :
    Kernel α (α × PUnit) :=
  Kernel.deterministic (fun x => (x, PUnit.unit)) (by measurability)

lemma assocKernel_naturality_type
    (f₁ : Kernel X₁ Y₁) (f₂ : Kernel X₂ Y₂) (f₃ : Kernel X₃ Y₃)
    [IsMarkovKernel f₁] [IsMarkovKernel f₂] [IsMarkovKernel f₃] :
    assocKernel Y₁ Y₂ Y₃ ∘ₖ ((f₁ ∥ₖ f₂) ∥ₖ f₃) =
      (f₁ ∥ₖ (f₂ ∥ₖ f₃)) ∘ₖ assocKernel X₁ X₂ X₃ := by
  letI : IsSFiniteKernel f₁ := by infer_instance
  letI : IsSFiniteKernel f₂ := by infer_instance
  letI : IsSFiniteKernel f₃ := by infer_instance
  letI : IsSFiniteKernel (f₁ ∥ₖ f₂) := by infer_instance
  letI : IsSFiniteKernel (f₂ ∥ₖ f₃) := by infer_instance
  ext p s hs
  rcases p with ⟨⟨x₁, x₂⟩, x₃⟩
  have hL : assocKernel Y₁ Y₂ Y₃ ∘ₖ ((f₁ ∥ₖ f₂) ∥ₖ f₃) =
      Kernel.map (((f₁ ∥ₖ f₂) ∥ₖ f₃)) MeasurableEquiv.prodAssoc := by
    simpa [assocKernel] using
      (Kernel.deterministic_comp_eq_map (f := MeasurableEquiv.prodAssoc)
        (hf := MeasurableEquiv.measurable _) (((f₁ ∥ₖ f₂) ∥ₖ f₃)))
  have hR : (f₁ ∥ₖ (f₂ ∥ₖ f₃)) ∘ₖ assocKernel X₁ X₂ X₃ =
      Kernel.comap (f₁ ∥ₖ (f₂ ∥ₖ f₃)) MeasurableEquiv.prodAssoc
        (MeasurableEquiv.measurable _) := by
    simpa [assocKernel] using
      (Kernel.comp_deterministic_eq_comap (κ := (f₁ ∥ₖ (f₂ ∥ₖ f₃)))
        (g := MeasurableEquiv.prodAssoc) (hg := MeasurableEquiv.measurable _))
  rw [hL, Kernel.map_apply _ (MeasurableEquiv.measurable _), hR, Kernel.comap_apply]
  simpa [Kernel.parallelComp_apply] using congrArg (fun μ => μ s)
    (Measure.prodAssoc_prod (μ := f₁ x₁) (ν := f₂ x₂) (τ := f₃ x₃))

lemma punitLeftUnitor_naturality_type
    {X Y : Type u} [MeasurableSpace X] [MeasurableSpace Y]
    (f : Kernel X Y) [IsMarkovKernel f] :
    punitLeftUnitorKernel Y ∘ₖ ((Kernel.id : Kernel PUnit PUnit) ∥ₖ f) =
      f ∘ₖ punitLeftUnitorKernel X := by
  letI : IsSFiniteKernel f := by infer_instance
  ext p s hs
  rcases p with ⟨u, x⟩
  cases u
  have hL : punitLeftUnitorKernel Y ∘ₖ ((Kernel.id : Kernel PUnit PUnit) ∥ₖ f) =
      Kernel.map ((Kernel.id : Kernel PUnit PUnit) ∥ₖ f) Prod.snd := by
    simpa [punitLeftUnitorKernel] using
      (Kernel.deterministic_comp_eq_map (f := Prod.snd) (hf := measurable_snd)
        ((Kernel.id : Kernel PUnit PUnit) ∥ₖ f))
  have hR : f ∘ₖ punitLeftUnitorKernel X = Kernel.comap f Prod.snd measurable_snd := by
    simpa [punitLeftUnitorKernel] using
      (Kernel.comp_deterministic_eq_comap (κ := f) (g := Prod.snd) (hg := measurable_snd))
  rw [hL, Kernel.map_apply _ measurable_snd, hR, Kernel.comap_apply]
  simp [Kernel.parallelComp_apply, Kernel.id_apply, Measure.map_snd_prod]

lemma punitRightUnitor_naturality_type
    {X Y : Type u} [MeasurableSpace X] [MeasurableSpace Y]
    (f : Kernel X Y) [IsMarkovKernel f] :
    punitRightUnitorKernel Y ∘ₖ (f ∥ₖ (Kernel.id : Kernel PUnit PUnit)) =
      f ∘ₖ punitRightUnitorKernel X := by
  letI : IsSFiniteKernel f := by infer_instance
  ext p s hs
  rcases p with ⟨x, u⟩
  cases u
  have hL : punitRightUnitorKernel Y ∘ₖ (f ∥ₖ (Kernel.id : Kernel PUnit PUnit)) =
      Kernel.map (f ∥ₖ (Kernel.id : Kernel PUnit PUnit)) Prod.fst := by
    simpa [punitRightUnitorKernel] using
      (Kernel.deterministic_comp_eq_map (f := Prod.fst) (hf := measurable_fst)
        (f ∥ₖ (Kernel.id : Kernel PUnit PUnit)))
  have hR : f ∘ₖ punitRightUnitorKernel X = Kernel.comap f Prod.fst measurable_fst := by
    simpa [punitRightUnitorKernel] using
      (Kernel.comp_deterministic_eq_comap (κ := f) (g := Prod.fst) (hg := measurable_fst))
  rw [hL, Kernel.map_apply _ measurable_fst, hR, Kernel.comap_apply]
  simp [Kernel.parallelComp_apply, Kernel.id_apply, Measure.map_fst_prod]

section

variable {W X Y Z : Type u}
variable [MeasurableSpace W] [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]

noncomputable def pentagonTarget :
    Kernel (((W × X) × Y) × Z) (W × (X × (Y × Z))) :=
  Kernel.deterministic (fun p => (p.1.1.1, (p.1.1.2, (p.1.2, p.2)))) (by measurability)

lemma pentagon_type :
    ((Kernel.id : Kernel W W) ∥ₖ assocKernel X Y Z) ∘ₖ assocKernel W (X × Y) Z ∘ₖ
      (assocKernel W X Y ∥ₖ (Kernel.id : Kernel Z Z)) =
        assocKernel W X (Y × Z) ∘ₖ assocKernel (W × X) Y Z := by
  calc
    ((Kernel.id : Kernel W W) ∥ₖ assocKernel X Y Z) ∘ₖ assocKernel W (X × Y) Z ∘ₖ
        (assocKernel W X Y ∥ₖ (Kernel.id : Kernel Z Z)) = pentagonTarget := by
      rw [Kernel.id, Kernel.id, assocKernel, assocKernel, assocKernel, pentagonTarget]
      repeat rw [Kernel.deterministic_parallelComp_deterministic]
      repeat rw [Kernel.deterministic_comp_deterministic]
      apply Kernel.deterministic_congr
      funext p
      rcases p with ⟨⟨⟨w, x⟩, y⟩, z⟩
      rfl
    _ = assocKernel W X (Y × Z) ∘ₖ assocKernel (W × X) Y Z := by
      rw [assocKernel, assocKernel, pentagonTarget]
      repeat rw [Kernel.deterministic_comp_deterministic]
      apply Kernel.deterministic_congr
      funext p
      rcases p with ⟨⟨⟨w, x⟩, y⟩, z⟩
      rfl

noncomputable def triangleTarget : Kernel ((X × PUnit) × Y) (X × Y) :=
  Kernel.deterministic (fun p => (p.1.1, p.2)) (by measurability)

lemma triangle_type :
    ((Kernel.id : Kernel X X) ∥ₖ punitLeftUnitorKernel Y) ∘ₖ assocKernel X PUnit Y =
      punitRightUnitorKernel X ∥ₖ (Kernel.id : Kernel Y Y) := by
  calc
    ((Kernel.id : Kernel X X) ∥ₖ punitLeftUnitorKernel Y) ∘ₖ assocKernel X PUnit Y =
        triangleTarget := by
      rw [Kernel.id, punitLeftUnitorKernel, assocKernel, triangleTarget]
      repeat rw [Kernel.deterministic_parallelComp_deterministic]
      repeat rw [Kernel.deterministic_comp_deterministic]
      apply Kernel.deterministic_congr
      funext p
      rcases p with ⟨⟨x, u⟩, y⟩
      cases u
      rfl
    _ = punitRightUnitorKernel X ∥ₖ (Kernel.id : Kernel Y Y) := by
      rw [Kernel.id, punitRightUnitorKernel, triangleTarget]
      rw [Kernel.deterministic_parallelComp_deterministic]
      apply Kernel.deterministic_congr
      funext p
      rcases p with ⟨x, y⟩
      rfl

end
end KernelLevel

/-- Bundled measurable spaces with Markov kernels as morphisms. -/
structure StochMarkov where
  α : Type u
  inst : MeasurableSpace α

attribute [instance] StochMarkov.inst
instance : CoeSort StochMarkov (Type u) := ⟨StochMarkov.α⟩

namespace StochMarkov

/-- Morphisms in `StochMarkov` are Markov kernels. -/
abbrev Hom (X Y : StochMarkov) := {κ : Kernel X Y // IsMarkovKernel κ}

instance {X Y : StochMarkov} : Coe (Hom X Y) (Kernel X Y) := ⟨Subtype.val⟩

instance {X Y : StochMarkov} (f : Hom X Y) : IsSFiniteKernel (f : Kernel X Y) := by
  letI : IsMarkovKernel (f : Kernel X Y) := f.2
  letI : IsFiniteKernel (f : Kernel X Y) := by infer_instance
  infer_instance

noncomputable instance : Category.{u} StochMarkov where
  Hom X Y := Hom X Y
  id X := ⟨Kernel.id, by infer_instance⟩
  comp f g := by
    letI : IsMarkovKernel f.1 := f.2
    letI : IsMarkovKernel g.1 := g.2
    have h : IsMarkovKernel (g.1 ∘ₖ f.1) := by infer_instance
    exact ⟨g.1 ∘ₖ f.1, h⟩
  id_comp f := by
    apply Subtype.ext
    exact Kernel.comp_id f.1
  comp_id f := by
    apply Subtype.ext
    exact Kernel.id_comp f.1
  assoc f g h := by
    apply Subtype.ext
    simpa using (Kernel.comp_assoc h.1 g.1 f.1).symm

/-- Tensor product on objects is the measurable product. -/
noncomputable def tensorObj (X Y : StochMarkov) : StochMarkov :=
  ⟨X × Y, inferInstance⟩

/-- The tensor unit is `PUnit`, which keeps the coherence proofs universe-safe. -/
def tensorUnit : StochMarkov := ⟨PUnit, inferInstance⟩

noncomputable def pLeftUnitorKernel (X : StochMarkov) : Kernel (PUnit × X) X :=
  punitLeftUnitorKernel X

noncomputable def pLeftUnitorKernelInv (X : StochMarkov) : Kernel X (PUnit × X) :=
  punitLeftUnitorKernelInv X

noncomputable def pRightUnitorKernel (X : StochMarkov) : Kernel (X × PUnit) X :=
  punitRightUnitorKernel X

noncomputable def pRightUnitorKernelInv (X : StochMarkov) : Kernel X (X × PUnit) :=
  punitRightUnitorKernelInv X

lemma assocKernel_isMarkov (X Y Z : StochMarkov) : IsMarkovKernel (assocKernel X Y Z) := by
  dsimp [assocKernel]
  infer_instance

lemma assocKernelInv_isMarkov (X Y Z : StochMarkov) :
    IsMarkovKernel (assocKernelInv X Y Z) := by
  dsimp [assocKernelInv]
  infer_instance

lemma pLeftUnitorKernel_isMarkov (X : StochMarkov) :
    IsMarkovKernel (pLeftUnitorKernel X) := by
  dsimp [pLeftUnitorKernel, punitLeftUnitorKernel]
  infer_instance

lemma pLeftUnitorKernelInv_isMarkov (X : StochMarkov) :
    IsMarkovKernel (pLeftUnitorKernelInv X) := by
  dsimp [pLeftUnitorKernelInv, punitLeftUnitorKernelInv]
  infer_instance

lemma pRightUnitorKernel_isMarkov (X : StochMarkov) :
    IsMarkovKernel (pRightUnitorKernel X) := by
  dsimp [pRightUnitorKernel, punitRightUnitorKernel]
  infer_instance

lemma pRightUnitorKernelInv_isMarkov (X : StochMarkov) :
    IsMarkovKernel (pRightUnitorKernelInv X) := by
  dsimp [pRightUnitorKernelInv, punitRightUnitorKernelInv]
  infer_instance

/-- Tensor product on morphisms via parallel composition. -/
noncomputable def tensorHom {X₁ Y₁ X₂ Y₂ : StochMarkov} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    tensorObj X₁ X₂ ⟶ tensorObj Y₁ Y₂ := by
  have h : IsMarkovKernel (f.1 ∥ₖ g.1) := by
    letI : IsMarkovKernel f.1 := f.2
    letI : IsMarkovKernel g.1 := g.2
    infer_instance
  exact ⟨f.1 ∥ₖ g.1, h⟩

noncomputable def whiskerLeft (X : StochMarkov) {Y₁ Y₂ : StochMarkov} (f : Y₁ ⟶ Y₂) :
    tensorObj X Y₁ ⟶ tensorObj X Y₂ :=
  tensorHom (𝟙 X) f

noncomputable def whiskerRight {X₁ X₂ : StochMarkov} (f : X₁ ⟶ X₂) (Y : StochMarkov) :
    tensorObj X₁ Y ⟶ tensorObj X₂ Y :=
  tensorHom f (𝟙 Y)

lemma assocKernel_comp_inv (X Y Z : StochMarkov) :
    assocKernelInv X Y Z ∘ₖ assocKernel X Y Z = Kernel.id := by
  simp only [assocKernel, assocKernelInv, Kernel.id]
  rw [Kernel.deterministic_comp_deterministic]
  rfl

lemma assocKernel_inv_comp (X Y Z : StochMarkov) :
    assocKernel X Y Z ∘ₖ assocKernelInv X Y Z = Kernel.id := by
  simp only [assocKernel, assocKernelInv, Kernel.id]
  rw [Kernel.deterministic_comp_deterministic]
  rfl

lemma pLeftUnitorKernel_comp_inv (X : StochMarkov) :
    pLeftUnitorKernelInv X ∘ₖ pLeftUnitorKernel X = Kernel.id := by
  simp only [pLeftUnitorKernel, pLeftUnitorKernelInv,
    punitLeftUnitorKernel, punitLeftUnitorKernelInv]
  rw [Kernel.deterministic_comp_deterministic]
  ext ⟨u, x⟩
  cases u
  simp [Kernel.deterministic_apply, Kernel.id_apply]

lemma pLeftUnitorKernel_inv_comp (X : StochMarkov) :
    pLeftUnitorKernel X ∘ₖ pLeftUnitorKernelInv X = Kernel.id := by
  simp only [pLeftUnitorKernel, pLeftUnitorKernelInv,
    punitLeftUnitorKernel, punitLeftUnitorKernelInv, Kernel.id]
  rw [Kernel.deterministic_comp_deterministic]
  rfl

lemma pRightUnitorKernel_comp_inv (X : StochMarkov) :
    pRightUnitorKernelInv X ∘ₖ pRightUnitorKernel X = Kernel.id := by
  simp only [pRightUnitorKernel, pRightUnitorKernelInv,
    punitRightUnitorKernel, punitRightUnitorKernelInv]
  rw [Kernel.deterministic_comp_deterministic]
  ext ⟨x, u⟩
  cases u
  simp [Kernel.deterministic_apply, Kernel.id_apply]

lemma pRightUnitorKernel_inv_comp (X : StochMarkov) :
    pRightUnitorKernel X ∘ₖ pRightUnitorKernelInv X = Kernel.id := by
  simp only [pRightUnitorKernel, pRightUnitorKernelInv,
    punitRightUnitorKernel, punitRightUnitorKernelInv, Kernel.id]
  rw [Kernel.deterministic_comp_deterministic]
  rfl

noncomputable def associatorIso (X Y Z : StochMarkov) :
    tensorObj (tensorObj X Y) Z ≅ tensorObj X (tensorObj Y Z) where
  hom := ⟨assocKernel X Y Z, assocKernel_isMarkov X Y Z⟩
  inv := ⟨assocKernelInv X Y Z, assocKernelInv_isMarkov X Y Z⟩
  hom_inv_id := by
    apply Subtype.ext
    simpa using assocKernel_comp_inv X Y Z
  inv_hom_id := by
    apply Subtype.ext
    simpa using assocKernel_inv_comp X Y Z

noncomputable def leftUnitorIso (X : StochMarkov) : tensorObj tensorUnit X ≅ X where
  hom := ⟨pLeftUnitorKernel X, pLeftUnitorKernel_isMarkov X⟩
  inv := ⟨pLeftUnitorKernelInv X, pLeftUnitorKernelInv_isMarkov X⟩
  hom_inv_id := by
    apply Subtype.ext
    simpa using pLeftUnitorKernel_comp_inv X
  inv_hom_id := by
    apply Subtype.ext
    simpa using pLeftUnitorKernel_inv_comp X

noncomputable def rightUnitorIso (X : StochMarkov) : tensorObj X tensorUnit ≅ X where
  hom := ⟨pRightUnitorKernel X, pRightUnitorKernel_isMarkov X⟩
  inv := ⟨pRightUnitorKernelInv X, pRightUnitorKernelInv_isMarkov X⟩
  hom_inv_id := by
    apply Subtype.ext
    simpa using pRightUnitorKernel_comp_inv X
  inv_hom_id := by
    apply Subtype.ext
    simpa using pRightUnitorKernel_inv_comp X

noncomputable def monoidalCategory : MonoidalCategory StochMarkov := by
  letI : MonoidalCategoryStruct StochMarkov := {
    tensorObj := StochMarkov.tensorObj
    whiskerLeft := StochMarkov.whiskerLeft
    whiskerRight := StochMarkov.whiskerRight
    tensorHom := fun {X₁ Y₁ X₂ Y₂} f g => StochMarkov.tensorHom f g
    tensorUnit := StochMarkov.tensorUnit
    associator := StochMarkov.associatorIso
    leftUnitor := StochMarkov.leftUnitorIso
    rightUnitor := StochMarkov.rightUnitorIso
  }
  exact MonoidalCategory.ofTensorHom (C := StochMarkov)
    (id_tensorHom_id := by
      intro X Y
      apply Subtype.ext
      simpa [StochMarkov.tensorHom] using (parallelComp_id_id X Y))
    (id_tensorHom := by
      intro X Y₁ Y₂ f
      rfl)
    (tensorHom_id := by
      intro X₁ X₂ f Y
      rfl)
    (tensorHom_comp_tensorHom := by
      intro X₁ Y₁ Z₁ X₂ Y₂ Z₂ f₁ f₂ g₁ g₂
      letI : IsSFiniteKernel f₁.1 := by infer_instance
      letI : IsSFiniteKernel f₂.1 := by infer_instance
      letI : IsSFiniteKernel g₁.1 := by infer_instance
      letI : IsSFiniteKernel g₂.1 := by infer_instance
      apply Subtype.ext
      simpa [StochMarkov.tensorHom] using
        (Kernel.parallelComp_comp_parallelComp (κ := f₁.1) (η := g₁.1)
          (κ' := f₂.1) (η' := g₂.1)))
    (associator_naturality := by
      intro X₁ X₂ X₃ Y₁ Y₂ Y₃ f₁ f₂ f₃
      letI : IsMarkovKernel f₁.1 := f₁.2
      letI : IsMarkovKernel f₂.1 := f₂.2
      letI : IsMarkovKernel f₃.1 := f₃.2
      apply Subtype.ext
      simpa [StochMarkov.tensorHom, associatorIso] using
        (assocKernel_naturality_type (f₁ := f₁.1) (f₂ := f₂.1) (f₃ := f₃.1)))
    (leftUnitor_naturality := by
      intro X Y f
      letI : IsMarkovKernel f.1 := f.2
      apply Subtype.ext
      simpa [StochMarkov.tensorHom, leftUnitorIso, pLeftUnitorKernel, punitLeftUnitorKernel] using
        (punitLeftUnitor_naturality_type (f := f.1)))
    (rightUnitor_naturality := by
      intro X Y f
      letI : IsMarkovKernel f.1 := f.2
      apply Subtype.ext
      simpa [StochMarkov.tensorHom, rightUnitorIso, pRightUnitorKernel,
        punitRightUnitorKernel] using
        (punitRightUnitor_naturality_type (f := f.1)))
    (pentagon := by
      intro W X Y Z
      apply Subtype.ext
      simpa [StochMarkov.tensorHom, associatorIso] using
        (pentagon_type (W := W) (X := X) (Y := Y) (Z := Z)))
    (triangle := by
      intro X Y
      apply Subtype.ext
      simpa [StochMarkov.tensorHom, associatorIso, leftUnitorIso, rightUnitorIso,
        pLeftUnitorKernel, pRightUnitorKernel, punitLeftUnitorKernel,
        punitRightUnitorKernel] using
        (triangle_type (X := X) (Y := Y)))

noncomputable instance : MonoidalCategory StochMarkov := monoidalCategory

end StochMarkov

end CpmProofs
