import CpmProofs.KanBridge
import CpmProofs.EnrichedKanExtension
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Closed.Enrichment

/-!

*Source: `EnrichedBridge.lean`*

# Specializing the abstract enriched formula to the concrete bridge

This file makes precise the remaining step between the local abstract enriched
Kan-extension interface and the concrete bridge theorem from `KanBridge.lean`.

The key observations are:

* `lanValue D hD κ f` is just `integrateAlong κ f`,
* a point of the weighted cocone object for a pointwise enriched left Kan
  extension determines an ordinary morphism by the representing isomorphism, and
* every kernel `κ` canonically determines such a weighted-cocone point by
  transposing `e.hom ≫ κ` through the representing isomorphism.

Because the stochastic self-enrichment is still incomplete, the file keeps the
missing enriched data explicit:

* `[MonoidalCategory MeasObj] [MonoidalClosed MeasObj]`,
* an explicit `HasEnrichedHom` family on the functor category, and
* the existence of the relevant pointwise enriched left Kan-extension objects.

Under those assumptions, we can already prove that the abstract enriched value
agrees with `lanValue`, satisfies the global factorization formula, and inherits
`IsStochKanExtension`; the previous identification hypothesis is now discharged
internally by the canonical weighted-cocone point attached to `κ`.

| # | Result | Status |
|---|--------|--------|
| 39 | `lanValue_eq_integrateAlong` | ✅ |
| 40 | `kernelFromWeightedPoint` | ✅ |
| 41 | `weightedPointOfKernel` | ✅ |
| 42 | `abstractLanValueFromEnriched_eq_lanValue` | ✅ |
| 43 | `abstractLanValueOfKernelFromEnriched_eq_lanValue` | ✅ |
| 44 | `abstractLanValueOfKernelFromEnriched_integral_factorization` | ✅ |
| 45 | `abstractLanValueOfKernelFromEnriched_isStochKanExtension` | ✅ |
-/

noncomputable section

open CategoryTheory Opposite ProbabilityTheory MeasureTheory
open scoped MonoidalCategory MonoidalClosed

namespace CpmProofs

/-- The pointwise stochastic Kan-extension value is exactly integration along
the conditional kernel. -/
theorem lanValue_eq_integrateAlong
    {X Y : MeasObj}
    (D : X → Y) (_hD : Measurable D) (κ : Kernel Y X) (f : X → ℝ) :
    lanValue D _hD κ f = integrateAlong κ f := rfl

section Abstract

variable [MonoidalCategory MeasObj] [MonoidalClosed MeasObj]

scoped instance stochEnrichedOrdinaryCategorySelf : EnrichedOrdinaryCategory MeasObj MeasObj :=
  CategoryTheory.MonoidalClosed.enrichedOrdinaryCategorySelf MeasObj

variable {A : Type*} [Category A]
variable (F G : A ⥤ MeasObj)

/-- A point of the weighted cocone object determines an ordinary morphism out of
the pointwise enriched left Kan-extension object via the representing
isomorphism. -/
noncomputable def PointwiseEnrichedLeftKanExtension.kernelFromWeightedPoint
    (hHom : ∀ F₁ F₂ : Aᵒᵖ ⥤ MeasObj,
      CategoryTheory.Enriched.FunctorCategory.HasEnrichedHom MeasObj F₁ F₂)
    [∀ (b X : MeasObj), HasPointwiseEnrichedLeftKanExtensionObj (V := MeasObj) F G b X]
    (lan : PointwiseEnrichedLeftKanExtension (V := MeasObj) F G)
    (b X : MeasObj)
    (ω : (𝟙_ MeasObj) ⟶ WeightedCoconeObj
      (V := MeasObj) (W := leftKanWeight MeasObj F b) G X) :
    lan.obj b ⟶ X := by
  letI := hHom
  exact (CategoryTheory.eHomEquiv MeasObj (X := lan.obj b) (Y := X)).symm
    (ω ≫ (WeightedColimit.descIso (V := MeasObj)
      (W := leftKanWeight MeasObj F b) (F := G)
      (colim := PointwiseEnrichedLeftKanExtension.colimit
        (V := MeasObj) (F := F) (G := G) lan b)
      (X := X)).inv)

/-- Every ordinary kernel `κ : b ⟶ X` canonically determines a point of the
weighted cocone object, by transposing `e.hom ≫ κ` through the enriched-hom
equivalence and then across the representing isomorphism. -/
noncomputable def PointwiseEnrichedLeftKanExtension.weightedPointOfKernel
    (hHom : ∀ F₁ F₂ : Aᵒᵖ ⥤ MeasObj,
      CategoryTheory.Enriched.FunctorCategory.HasEnrichedHom MeasObj F₁ F₂)
    [∀ (b X : MeasObj), HasPointwiseEnrichedLeftKanExtensionObj (V := MeasObj) F G b X]
    (lan : PointwiseEnrichedLeftKanExtension (V := MeasObj) F G)
    {b X : MeasObj} (e : lan.obj b ≅ b) (κ : b ⟶ X) :
    (𝟙_ MeasObj) ⟶ WeightedCoconeObj
      (V := MeasObj) (W := leftKanWeight MeasObj F b) G X := by
  letI := hHom
  exact ((CategoryTheory.eHomEquiv MeasObj (X := lan.obj b) (Y := X)) (e.hom ≫ κ)) ≫
    (WeightedColimit.descIso (V := MeasObj)
      (W := leftKanWeight MeasObj F b) (F := G)
      (colim := PointwiseEnrichedLeftKanExtension.colimit
        (V := MeasObj) (F := F) (G := G) lan b)
      (X := X)).hom

/-- The canonical weighted-cocone point attached to `κ` recovers `e.hom ≫ κ`
when translated back through the representing isomorphism. -/
theorem PointwiseEnrichedLeftKanExtension.kernelFromWeightedPoint_weightedPointOfKernel
    (hHom : ∀ F₁ F₂ : Aᵒᵖ ⥤ MeasObj,
      CategoryTheory.Enriched.FunctorCategory.HasEnrichedHom MeasObj F₁ F₂)
    [∀ (b X : MeasObj), HasPointwiseEnrichedLeftKanExtensionObj (V := MeasObj) F G b X]
    (lan : PointwiseEnrichedLeftKanExtension (V := MeasObj) F G)
    {b X : MeasObj} (e : lan.obj b ≅ b) (κ : b ⟶ X) :
    PointwiseEnrichedLeftKanExtension.kernelFromWeightedPoint (F := F) (G := G)
      hHom lan b X
      (PointwiseEnrichedLeftKanExtension.weightedPointOfKernel (F := F) (G := G)
        hHom lan e κ) =
      e.hom ≫ κ := by
  letI := hHom
  simp [PointwiseEnrichedLeftKanExtension.weightedPointOfKernel,
    PointwiseEnrichedLeftKanExtension.kernelFromWeightedPoint]

/-- After precomposing by the chosen identification `lan.obj b ≅ b`, the
canonical weighted-cocone point recovers the original kernel `κ`. -/
theorem PointwiseEnrichedLeftKanExtension.inv_kernelFromWeightedPoint_weightedPointOfKernel
    (hHom : ∀ F₁ F₂ : Aᵒᵖ ⥤ MeasObj,
      CategoryTheory.Enriched.FunctorCategory.HasEnrichedHom MeasObj F₁ F₂)
    [∀ (b X : MeasObj), HasPointwiseEnrichedLeftKanExtensionObj (V := MeasObj) F G b X]
    (lan : PointwiseEnrichedLeftKanExtension (V := MeasObj) F G)
    {b X : MeasObj} (e : lan.obj b ≅ b) (κ : b ⟶ X) :
    e.inv ≫ PointwiseEnrichedLeftKanExtension.kernelFromWeightedPoint (F := F) (G := G)
      hHom lan b X
      (PointwiseEnrichedLeftKanExtension.weightedPointOfKernel (F := F) (G := G)
        hHom lan e κ) = κ := by
  rw [PointwiseEnrichedLeftKanExtension.kernelFromWeightedPoint_weightedPointOfKernel
    (F := F) (G := G) hHom lan e κ]
  simp

/-- Applying the abstract enriched pointwise formula to a weighted-cocone point
and then integrating an observable `f` against the resulting kernel gives a
concrete candidate stochastic Kan-extension value on `Y`. -/
noncomputable def abstractLanValueFromEnriched
    {X Y : MeasObj}
    (hHom : ∀ F₁ F₂ : Aᵒᵖ ⥤ MeasObj,
      CategoryTheory.Enriched.FunctorCategory.HasEnrichedHom MeasObj F₁ F₂)
    [∀ (b X' : MeasObj), HasPointwiseEnrichedLeftKanExtensionObj (V := MeasObj) F G b X']
    (lan : PointwiseEnrichedLeftKanExtension (V := MeasObj) F G)
    (e : lan.obj Y ≅ Y)
    (ω : (𝟙_ MeasObj) ⟶ WeightedCoconeObj
      (V := MeasObj) (W := leftKanWeight MeasObj F Y) G X)
    (f : X → ℝ) : Y → ℝ :=
  integrateAlong
    (e.inv ≫ PointwiseEnrichedLeftKanExtension.kernelFromWeightedPoint
      (F := F) (G := G) hHom lan Y X ω)
    f

/-- Once the missing stochastic self-enrichment data is instantiated so that
the abstract weighted-cocone point recovers the conditional kernel `κ`, the
abstract enriched value reduces to the concrete `lanValue`. -/
theorem abstractLanValueFromEnriched_eq_lanValue
    {X Y : MeasObj}
    (hHom : ∀ F₁ F₂ : Aᵒᵖ ⥤ MeasObj,
      CategoryTheory.Enriched.FunctorCategory.HasEnrichedHom MeasObj F₁ F₂)
    [∀ (b X' : MeasObj), HasPointwiseEnrichedLeftKanExtensionObj (V := MeasObj) F G b X']
    (D : X → Y) (hD : Measurable D) (κ : Kernel Y X) (f : X → ℝ)
    (lan : PointwiseEnrichedLeftKanExtension (V := MeasObj) F G)
    (e : lan.obj Y ≅ Y)
    (ω : (𝟙_ MeasObj) ⟶ WeightedCoconeObj
      (V := MeasObj) (W := leftKanWeight MeasObj F Y) G X)
    (hω : e.inv ≫ PointwiseEnrichedLeftKanExtension.kernelFromWeightedPoint
      (F := F) (G := G) hHom lan Y X ω = κ) :
    abstractLanValueFromEnriched (F := F) (G := G) hHom lan e ω f =
      lanValue D hD κ f := by
  rw [lanValue_eq_integrateAlong (D := D) (κ := κ) (f := f)]
  simp [abstractLanValueFromEnriched, hω]

/-- The same specialization turns the abstract enriched pointwise formula into
the concrete global disintegration identity from the bridge theorem. -/
theorem abstractLanValueFromEnriched_integral_factorization
    {X Y : MeasObj}
    (hHom : ∀ F₁ F₂ : Aᵒᵖ ⥤ MeasObj,
      CategoryTheory.Enriched.FunctorCategory.HasEnrichedHom MeasObj F₁ F₂)
    [∀ (b X' : MeasObj), HasPointwiseEnrichedLeftKanExtensionObj (V := MeasObj) F G b X']
    (D : X → Y) (hD : Measurable D)
    (μ : Measure X) (κ : Kernel Y X) (hκ : IsCondKernelMap D μ κ)
    (f : X → ℝ) (hf_meas : AEStronglyMeasurable f μ) (hf_int : Integrable f μ)
    (lan : PointwiseEnrichedLeftKanExtension (V := MeasObj) F G)
    (e : lan.obj Y ≅ Y)
    (ω : (𝟙_ MeasObj) ⟶ WeightedCoconeObj
      (V := MeasObj) (W := leftKanWeight MeasObj F Y) G X)
    (hω : e.inv ≫ PointwiseEnrichedLeftKanExtension.kernelFromWeightedPoint
      (F := F) (G := G) hHom lan Y X ω = κ) :
    (∫ x, f x ∂μ) =
      ∫ y, abstractLanValueFromEnriched (F := F) (G := G) hHom lan e ω f y
        ∂(Measure.map D μ) := by
  rw [abstractLanValueFromEnriched_eq_lanValue (F := F) (G := G) hHom
    (D := D) (hD := hD) (κ := κ) (f := f) (lan := lan) (e := e) (ω := ω) hω]
  exact lan_eq_integral_of_condKernel D hD μ κ hκ f hf_meas hf_int

/-- The same specialization packages the abstract enriched pointwise formula as
an `IsStochKanExtension`, i.e. it inherits the set-integral factorization
predicate from Part 4. -/
theorem abstractLanValueFromEnriched_isStochKanExtension
    {X Y : MeasObj}
    (hHom : ∀ F₁ F₂ : Aᵒᵖ ⥤ MeasObj,
      CategoryTheory.Enriched.FunctorCategory.HasEnrichedHom MeasObj F₁ F₂)
    [∀ (b X' : MeasObj), HasPointwiseEnrichedLeftKanExtensionObj (V := MeasObj) F G b X']
    (D : X → Y) (hD : Measurable D)
    (μ : Measure X) (κ : Kernel Y X) (hκ : IsCondKernelMap D μ κ)
    (f : X → ℝ) (hf_meas : AEStronglyMeasurable f μ) (hf_int : Integrable f μ)
    (lan : PointwiseEnrichedLeftKanExtension (V := MeasObj) F G)
    (e : lan.obj Y ≅ Y)
    (ω : (𝟙_ MeasObj) ⟶ WeightedCoconeObj
      (V := MeasObj) (W := leftKanWeight MeasObj F Y) G X)
    (hω : e.inv ≫ PointwiseEnrichedLeftKanExtension.kernelFromWeightedPoint
      (F := F) (G := G) hHom lan Y X ω = κ) :
    IsStochKanExtension D μ
      (abstractLanValueFromEnriched (F := F) (G := G) hHom lan e ω f) f := by
  rw [abstractLanValueFromEnriched_eq_lanValue (F := F) (G := G) hHom
    (D := D) (hD := hD) (κ := κ) (f := f) (lan := lan) (e := e) (ω := ω) hω]
  exact lanValue_isStochKanExtension D hD μ κ hκ f hf_meas hf_int

/-- The canonical enriched value attached directly to a kernel `κ`, obtained by
feeding `κ` through `weightedPointOfKernel` before evaluating the abstract
formula. -/
noncomputable def abstractLanValueOfKernelFromEnriched
    {X Y : MeasObj}
    (hHom : ∀ F₁ F₂ : Aᵒᵖ ⥤ MeasObj,
      CategoryTheory.Enriched.FunctorCategory.HasEnrichedHom MeasObj F₁ F₂)
    [∀ (b X' : MeasObj), HasPointwiseEnrichedLeftKanExtensionObj (V := MeasObj) F G b X']
    (lan : PointwiseEnrichedLeftKanExtension (V := MeasObj) F G)
    (e : lan.obj Y ≅ Y) (κ : Y ⟶ X) (f : X → ℝ) : Y → ℝ :=
  abstractLanValueFromEnriched (F := F) (G := G) hHom lan e
    (PointwiseEnrichedLeftKanExtension.weightedPointOfKernel (F := F) (G := G)
      hHom lan e κ) f

/-- Using the canonical weighted-cocone point of `κ`, the abstract enriched
pointwise value reduces directly to the concrete `lanValue`, with no separate
identification hypothesis. -/
theorem abstractLanValueOfKernelFromEnriched_eq_lanValue
    {X Y : MeasObj}
    (hHom : ∀ F₁ F₂ : Aᵒᵖ ⥤ MeasObj,
      CategoryTheory.Enriched.FunctorCategory.HasEnrichedHom MeasObj F₁ F₂)
    [∀ (b X' : MeasObj), HasPointwiseEnrichedLeftKanExtensionObj (V := MeasObj) F G b X']
    (D : X → Y) (hD : Measurable D) (κ : Kernel Y X) (f : X → ℝ)
    (lan : PointwiseEnrichedLeftKanExtension (V := MeasObj) F G)
    (e : lan.obj Y ≅ Y) :
    abstractLanValueOfKernelFromEnriched (F := F) (G := G) hHom lan e κ f =
      lanValue D hD κ f := by
  refine abstractLanValueFromEnriched_eq_lanValue (F := F) (G := G) hHom
    (D := D) (hD := hD) (κ := κ) (f := f) (lan := lan) (e := e)
    (ω := PointwiseEnrichedLeftKanExtension.weightedPointOfKernel (F := F) (G := G)
      hHom lan e κ) ?_
  exact PointwiseEnrichedLeftKanExtension.inv_kernelFromWeightedPoint_weightedPointOfKernel
    (F := F) (G := G) hHom lan e κ

/-- The canonical abstract enriched value attached to `κ` satisfies the same
global factorization formula as the concrete bridge theorem. -/
theorem abstractLanValueOfKernelFromEnriched_integral_factorization
    {X Y : MeasObj}
    (hHom : ∀ F₁ F₂ : Aᵒᵖ ⥤ MeasObj,
      CategoryTheory.Enriched.FunctorCategory.HasEnrichedHom MeasObj F₁ F₂)
    [∀ (b X' : MeasObj), HasPointwiseEnrichedLeftKanExtensionObj (V := MeasObj) F G b X']
    (D : X → Y) (hD : Measurable D)
    (μ : Measure X) (κ : Kernel Y X) (hκ : IsCondKernelMap D μ κ)
    (f : X → ℝ) (hf_meas : AEStronglyMeasurable f μ) (hf_int : Integrable f μ)
    (lan : PointwiseEnrichedLeftKanExtension (V := MeasObj) F G)
    (e : lan.obj Y ≅ Y) :
    (∫ x, f x ∂μ) =
      ∫ y, abstractLanValueOfKernelFromEnriched (F := F) (G := G) hHom lan e κ f y
        ∂(Measure.map D μ) := by
  rw [abstractLanValueOfKernelFromEnriched_eq_lanValue (F := F) (G := G) hHom
    (D := D) (hD := hD) (κ := κ) (f := f) (lan := lan) (e := e)]
  exact lan_eq_integral_of_condKernel D hD μ κ hκ f hf_meas hf_int

/-- The canonical abstract enriched value attached to `κ` also inherits the
stochastic universal property from Part 4. -/
theorem abstractLanValueOfKernelFromEnriched_isStochKanExtension
    {X Y : MeasObj}
    (hHom : ∀ F₁ F₂ : Aᵒᵖ ⥤ MeasObj,
      CategoryTheory.Enriched.FunctorCategory.HasEnrichedHom MeasObj F₁ F₂)
    [∀ (b X' : MeasObj), HasPointwiseEnrichedLeftKanExtensionObj (V := MeasObj) F G b X']
    (D : X → Y) (hD : Measurable D)
    (μ : Measure X) (κ : Kernel Y X) (hκ : IsCondKernelMap D μ κ)
    (f : X → ℝ) (hf_meas : AEStronglyMeasurable f μ) (hf_int : Integrable f μ)
    (lan : PointwiseEnrichedLeftKanExtension (V := MeasObj) F G)
    (e : lan.obj Y ≅ Y) :
    IsStochKanExtension D μ
      (abstractLanValueOfKernelFromEnriched (F := F) (G := G) hHom lan e κ f) f := by
  rw [abstractLanValueOfKernelFromEnriched_eq_lanValue (F := F) (G := G) hHom
    (D := D) (hD := hD) (κ := κ) (f := f) (lan := lan) (e := e)]
  exact lanValue_isStochKanExtension D hD μ κ hκ f hf_meas hf_int

end Abstract

end CpmProofs
