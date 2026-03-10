import Mathlib.CategoryTheory.Enriched.FunctorCategory
import Mathlib.CategoryTheory.Monoidal.Closed.Enrichment

/-!

*Source: `WeightedColimit.lean`*

# Weighted colimits

This file introduces a lightweight local notion of weighted colimit for
`V`-enriched categories. It is sufficient for the enriched Kan-extension
roadmap in `CpmProofs/Enriched.lean`.

For a diagram `F : J ⥤ C` and a weight `W : Jᵒᵖ ⥤ V`, the `V`-object of
weighted cocones with vertex `X : C` is defined as the enriched hom object

`[Jᵒᵖ, V](W, j ↦ (F j ⟶[V] X))`.

A weighted colimit of `F` by `W` is then an object `L : C` representing this
weighted cocone object.
-/

noncomputable section

universe v u₁ u₂ u₃

namespace CpmProofs

open CategoryTheory Opposite
open CategoryTheory.Enriched.FunctorCategory
open scoped MonoidalClosed

variable (V : Type u₁) [Category.{v} V] [MonoidalCategory V] [MonoidalClosed V]
variable {J : Type u₂} [Category.{v} J]
variable {C : Type u₃} [Category.{v} C] [EnrichedOrdinaryCategory V C]

/-- For `F : J ⥤ C` and `X : C`, this is the `Jᵒᵖ ⥤ V` diagram
`j ↦ (F j ⟶[V] X)` that appears in the weighted-colimit universal property. -/
@[simps]
def weightedHomDiagram (F : J ⥤ C) (X : C) : Jᵒᵖ ⥤ V where
  obj j := F.obj j.unop ⟶[V] X
  map f := CategoryTheory.eHomWhiskerRight V (F.map f.unop) X

/-- Postcomposition with `f : X ⟶ Y` induces a morphism between the weighted
hom diagrams for vertices `X` and `Y`. -/
@[simps]
def weightedHomDiagramMap (F : J ⥤ C) {X Y : C} (f : X ⟶ Y) :
    weightedHomDiagram V F X ⟶ weightedHomDiagram V F Y where
  app j := CategoryTheory.eHomWhiskerLeft V (F.obj j.unop) f
  naturality j j' g := by
    dsimp
    simpa using
      (CategoryTheory.eHom_whisker_exchange (V := V) (f := F.map g.unop) (g := f)).symm

/-- The assumption needed for the `V`-object of weighted cocones with vertex `X`
to exist. -/
abbrev HasWeightedCoconeObj (W : Jᵒᵖ ⥤ V) (F : J ⥤ C) (X : C) :=
  HasEnrichedHom V W (weightedHomDiagram V F X)

/-- The `V`-object of `W`-weighted cocones on `F` with vertex `X`. -/
abbrev WeightedCoconeObj (W : Jᵒᵖ ⥤ V) (F : J ⥤ C) (X : C)
    [HasWeightedCoconeObj (V := V) W F X] : V :=
  enrichedHom V W (weightedHomDiagram V F X)

/-- Postcomposition with `f : X ⟶ Y` induces a morphism between the
`V`-objects of weighted cocones with vertices `X` and `Y`. -/
def weightedCoconeMap (W : Jᵒᵖ ⥤ V) (F : J ⥤ C) {X Y : C} (f : X ⟶ Y)
    [HasWeightedCoconeObj (V := V) W F X]
    [HasWeightedCoconeObj (V := V) W F Y]
    [∀ F₁ F₂ : Jᵒᵖ ⥤ V, HasEnrichedHom V F₁ F₂] :
    WeightedCoconeObj (V := V) W F X ⟶ WeightedCoconeObj (V := V) W F Y := by
  letI : EnrichedOrdinaryCategory V V := by infer_instance
  letI : EnrichedOrdinaryCategory V (Jᵒᵖ ⥤ V) :=
    enrichedOrdinaryCategory (V := V) (J := Jᵒᵖ) (C := V)
  exact CategoryTheory.eHomWhiskerLeft V W (weightedHomDiagramMap V F f)

/-- The universal property of a `W`-weighted colimit of `F`, expressed as a
representing object for the `V`-object of weighted cocones. -/
structure IsWeightedColimit (W : Jᵒᵖ ⥤ V) (F : J ⥤ C) (L : C)
    [∀ X : C, HasWeightedCoconeObj (V := V) W F X]
    [∀ F₁ F₂ : Jᵒᵖ ⥤ V, HasEnrichedHom V F₁ F₂] where
  /-- The representing isomorphism
  `C(L, X) ≅ [Jᵒᵖ, V](W, j ↦ C(F j, X))`. -/
  desc : ∀ X : C, (L ⟶[V] X) ≅ WeightedCoconeObj (V := V) W F X
  /-- Naturality of `desc` in the vertex object. -/
  naturality : ∀ {X Y : C} (f : X ⟶ Y),
    CategoryTheory.eHomWhiskerLeft V L f ≫ (desc Y).hom =
      (desc X).hom ≫ weightedCoconeMap (V := V) W F f

/-- A weighted colimit packages the representing object together with its
universal property. -/
structure WeightedColimit (W : Jᵒᵖ ⥤ V) (F : J ⥤ C)
    [∀ X : C, HasWeightedCoconeObj (V := V) W F X]
    [∀ F₁ F₂ : Jᵒᵖ ⥤ V, HasEnrichedHom V F₁ F₂] where
  /-- The weighted colimit object. -/
  obj : C
  /-- The representing universal property. -/
  isWeightedColimit : IsWeightedColimit (V := V) W F obj

/-- The representing isomorphism associated to a weighted colimit. -/
abbrev WeightedColimit.descIso (W : Jᵒᵖ ⥤ V) (F : J ⥤ C)
    [∀ X : C, HasWeightedCoconeObj (V := V) W F X]
    [∀ F₁ F₂ : Jᵒᵖ ⥤ V, HasEnrichedHom V F₁ F₂]
    (colim : WeightedColimit (V := V) W F) (X : C) :
    (colim.obj ⟶[V] X) ≅ WeightedCoconeObj (V := V) W F X :=
  colim.isWeightedColimit.desc X

/-- Naturality of the weighted-colimit representing isomorphism. -/
@[reassoc]
lemma WeightedColimit.desc_hom_naturality (W : Jᵒᵖ ⥤ V) (F : J ⥤ C)
    [∀ X : C, HasWeightedCoconeObj (V := V) W F X]
    [∀ F₁ F₂ : Jᵒᵖ ⥤ V, HasEnrichedHom V F₁ F₂]
    (colim : WeightedColimit (V := V) W F) {X Y : C} (f : X ⟶ Y) :
    CategoryTheory.eHomWhiskerLeft V colim.obj f ≫ (colim.descIso (X := Y)).hom =
      (colim.descIso (X := X)).hom ≫ weightedCoconeMap (V := V) W F f :=
  colim.isWeightedColimit.naturality f

end CpmProofs
