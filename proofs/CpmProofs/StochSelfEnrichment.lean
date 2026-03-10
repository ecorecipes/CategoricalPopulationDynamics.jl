import CpmProofs.StochCat
import Mathlib.CategoryTheory.Monoidal.Closed.Enrichment
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.MeasurableSpace.Constructions

/-!

*Source: `StochSelfEnrichment.lean`*

# Stochastic self-enrichment scaffolding

This file isolates the remaining gap between the concrete stochastic category
from `CpmProofs.StochCat` and a full `MonoidalClosed` self-enrichment.

We define a candidate internal-hom object `kernelHomObj X Y` whose underlying
space consists of kernels `X ⟶ Y`, equipped with the pointwise measurable
structure coming from the map `κ ↦ (x ↦ κ x)`.

This gives a concrete place where the missing measurable-space work lives:

* we can talk about pointwise-measurable evaluation maps `κ ↦ κ x`,
* we can describe the underlying function induced by postcomposition,
* and once a genuine `MonoidalCategory`/`MonoidalClosed` structure is supplied,
  Mathlib already upgrades it to a self-enrichment automatically.

What is still missing for a full self-enrichment is a bona fide stochastic
tensor on morphisms together with a jointly measurable evaluation/curry-uncurry
adjunction for these kernel-hom objects.
-/

open CategoryTheory
open MeasureTheory
open ProbabilityTheory
open scoped MonoidalClosed

noncomputable section

namespace CpmProofs

/-- Candidate internal-hom object for stochastic self-enrichment:
the measurable space of kernels `X ⟶ Y`, equipped with the pointwise measurable
structure induced by the map into `X → Measure Y`. -/
def kernelHomObj (X Y : MeasObj) : MeasObj where
  α := Kernel X Y
  inst := MeasurableSpace.comap (fun κ : Kernel X Y => (κ : X → Measure Y)) inferInstance

/-- The defining map from the candidate kernel-hom object to the corresponding
function space is measurable by construction. -/
lemma measurable_kernel_toFun (X Y : MeasObj) :
    Measurable (fun κ : kernelHomObj X Y => ((show Kernel X Y from κ) : X → Measure Y)) := by
  exact Measurable.of_comap_le le_rfl

/-- Evaluation at a fixed point is measurable on the candidate kernel-hom object. -/
lemma measurable_kernel_eval (X Y : MeasObj) (x : X) :
    Measurable (fun κ : kernelHomObj X Y => ((show Kernel X Y from κ) : X → Measure Y) x) := by
  simpa using (Measurable.eval (a := (x : X)) (hg := measurable_kernel_toFun X Y))

/-- Evaluation of a kernel on a fixed measurable set is measurable on the
candidate kernel-hom object. -/
lemma measurable_kernel_apply (X Y : MeasObj) (x : X) {s : Set Y} (hs : MeasurableSet s) :
    Measurable (fun κ : kernelHomObj X Y => (show Kernel X Y from κ) x s) := by
  exact (Measure.measurable_coe hs).comp (measurable_kernel_eval X Y x)

/-- The expected underlying function on kernel-hom objects induced by
postcomposition with a kernel. The remaining self-enrichment gap is to show that
this participates in a full internal-hom adjunction. -/
def postcompKernelFun (X Y Z : MeasObj) (η : X ⟶ Y) : kernelHomObj Z X → kernelHomObj Z Y :=
  fun κ =>
    ({ toFun := fun z => (((show Kernel Z X from κ) z)).bind η
       measurable' := by
         exact (Measure.measurable_bind' η.measurable).comp ((show Kernel Z X from κ).measurable) } :
      Kernel Z Y)

section Abstract

variable [MonoidalCategory MeasObj] [MonoidalClosed MeasObj]

/-- Once a monoidal closed structure on the stochastic category is supplied,
Mathlib immediately upgrades it to a self-enrichment. -/
scoped instance stochEnrichedOrdinaryCategory : EnrichedOrdinaryCategory MeasObj MeasObj :=
  CategoryTheory.MonoidalClosed.enrichedOrdinaryCategorySelf MeasObj

/-- Under a hypothetical monoidal closed structure, this is the internal-hom
object used by stochastic self-enrichment. -/
abbrev stochInternalHom (X Y : MeasObj) : MeasObj :=
  (CategoryTheory.ihom X).obj Y

/-- Under a hypothetical monoidal closed structure, currying is the hom
equivalence that would package stochastic self-enrichment. -/
abbrev stochCurryEquiv (X Y Z : MeasObj) :=
  (CategoryTheory.ihom.adjunction X).homEquiv Y Z

end Abstract

end CpmProofs
