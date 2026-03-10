import CpmProofs.WeightedColimit

/-!

*Source: `EnrichedKanExtension.lean`*

# Enriched Kan extensions

This file adds a lightweight local interface for pointwise enriched left Kan
extensions. It is built directly from the weighted-colimit API in
`CpmProofs.WeightedColimit`.

For `F : A ⥤ B` and `G : A ⥤ C`, the pointwise enriched left Kan extension of
`G` along `F` at `b : B` is presented as a weighted colimit of `G` by the
representable weight `B(F-, b)`.
-/

noncomputable section

universe v u₁ u₂ u₃ u₄

namespace CpmProofs

open CategoryTheory Opposite
open CategoryTheory.Enriched.FunctorCategory
open scoped MonoidalClosed

variable (V : Type u₁) [Category.{v} V] [MonoidalCategory V] [MonoidalClosed V]
variable {A : Type u₂} [Category.{v} A]
variable {B : Type u₃} [Category.{v} B] [EnrichedOrdinaryCategory V B]
variable {C : Type u₄} [Category.{v} C] [EnrichedOrdinaryCategory V C]

/-- The representable weight `a ↦ B(F a, b)` used in the pointwise enriched
left Kan extension formula. -/
abbrev leftKanWeight (F : A ⥤ B) (b : B) : Aᵒᵖ ⥤ V :=
  weightedHomDiagram V F b

/-- A morphism `b ⟶ b'` in the target category induces a morphism between the
corresponding representable weights. -/
abbrev leftKanWeightMap (F : A ⥤ B) {b b' : B} (f : b ⟶ b') :
    leftKanWeight V F b ⟶ leftKanWeight V F b' :=
  weightedHomDiagramMap V F f

/-- Precomposition in the weight variable. -/
def weightedCoconeMapWeight {W W' : Aᵒᵖ ⥤ V} (G : A ⥤ C) {X : C} (η : W ⟶ W')
    [HasWeightedCoconeObj (V := V) W G X]
    [HasWeightedCoconeObj (V := V) W' G X]
    [∀ F₁ F₂ : Aᵒᵖ ⥤ V, HasEnrichedHom V F₁ F₂] :
    WeightedCoconeObj (V := V) W' G X ⟶ WeightedCoconeObj (V := V) W G X := by
  letI : EnrichedOrdinaryCategory V V := by infer_instance
  letI : EnrichedOrdinaryCategory V (Aᵒᵖ ⥤ V) :=
    enrichedOrdinaryCategory (V := V) (J := Aᵒᵖ) (C := V)
  exact CategoryTheory.eHomWhiskerRight V η (weightedHomDiagram V G X)

/-- A morphism of weights induces a morphism between weighted colimit objects. -/
def WeightedColimit.mapWeight {W W' : Aᵒᵖ ⥤ V} (G : A ⥤ C)
    [∀ X : C, HasWeightedCoconeObj (V := V) W G X]
    [∀ X : C, HasWeightedCoconeObj (V := V) W' G X]
    [∀ F₁ F₂ : Aᵒᵖ ⥤ V, HasEnrichedHom V F₁ F₂]
    (η : W ⟶ W') (colim : WeightedColimit (V := V) W G)
    (colim' : WeightedColimit (V := V) W' G) :
    colim.obj ⟶ colim'.obj := by
  refine (CategoryTheory.eHomEquiv V (X := colim.obj) (Y := colim'.obj)).symm ?_
  exact CategoryTheory.eId V colim'.obj ≫
    (colim'.descIso (W := W') (F := G) (X := colim'.obj)).hom ≫
      weightedCoconeMapWeight (V := V) (G := G) (W := W) (W' := W')
        (X := colim'.obj) η ≫
        (colim.descIso (W := W) (F := G) (X := colim'.obj)).inv

/-- Existence of the weighted cocone object needed to define the pointwise
enriched left Kan extension at `b`. -/
abbrev HasPointwiseEnrichedLeftKanExtensionObj
    (F : A ⥤ B) (G : A ⥤ C) (b : B) (X : C) :=
  HasWeightedCoconeObj (V := V) (W := leftKanWeight V F b) G X

/-- The pointwise enriched left Kan extension condition at a single object
`b : B`. -/
abbrev IsPointwiseEnrichedLeftKanExtensionAt
    (F : A ⥤ B) (G : A ⥤ C) (b : B) (L : C)
    [∀ X : C, HasPointwiseEnrichedLeftKanExtensionObj (V := V) F G b X]
    [∀ F₁ F₂ : Aᵒᵖ ⥤ V, HasEnrichedHom V F₁ F₂] :=
  IsWeightedColimit (V := V) (W := leftKanWeight V F b) G L

/-- A local pointwise enriched left Kan extension, packaged as a family of
weighted colimits. -/
structure PointwiseEnrichedLeftKanExtension (F : A ⥤ B) (G : A ⥤ C)
    [∀ (b : B) (X : C), HasPointwiseEnrichedLeftKanExtensionObj (V := V) F G b X]
    [∀ F₁ F₂ : Aᵒᵖ ⥤ V, HasEnrichedHom V F₁ F₂] where
  obj : B → C
  isPointwise : ∀ b : B, IsPointwiseEnrichedLeftKanExtensionAt (V := V) F G b (obj b)

/-- The weighted-colimit package at a fixed `b : B`. -/
abbrev PointwiseEnrichedLeftKanExtension.colimit (F : A ⥤ B) (G : A ⥤ C)
    [∀ (b : B) (X : C), HasPointwiseEnrichedLeftKanExtensionObj (V := V) F G b X]
    [∀ F₁ F₂ : Aᵒᵖ ⥤ V, HasEnrichedHom V F₁ F₂]
    (lan : PointwiseEnrichedLeftKanExtension (V := V) F G) (b : B) :
    WeightedColimit (V := V) (leftKanWeight V F b) G :=
  { obj := lan.obj b, isWeightedColimit := lan.isPointwise b }

/-- The canonical map on pointwise enriched left Kan extension objects induced
by a morphism in `B`. -/
def PointwiseEnrichedLeftKanExtension.map (F : A ⥤ B) (G : A ⥤ C)
    [∀ (b : B) (X : C), HasPointwiseEnrichedLeftKanExtensionObj (V := V) F G b X]
    [∀ F₁ F₂ : Aᵒᵖ ⥤ V, HasEnrichedHom V F₁ F₂]
    (lan : PointwiseEnrichedLeftKanExtension (V := V) F G) {b b' : B} (f : b ⟶ b') :
    lan.obj b ⟶ lan.obj b' :=
  WeightedColimit.mapWeight (V := V) (G := G) (η := leftKanWeightMap V F f)
    (PointwiseEnrichedLeftKanExtension.colimit (V := V) (F := F) (G := G) lan b)
    (PointwiseEnrichedLeftKanExtension.colimit (V := V) (F := F) (G := G) lan b')

end CpmProofs
