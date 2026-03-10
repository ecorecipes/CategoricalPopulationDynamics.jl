import CpmProofs.KanBridge
import CpmProofs.EnrichedKanExtension
import CpmProofs.EnrichedBridge
import CpmProofs.StochSelfEnrichment
import Mathlib.CategoryTheory.Enriched.Basic
import Mathlib.CategoryTheory.Enriched.Ordinary.Basic
import Mathlib.CategoryTheory.Category.Init

/-!

*Source: `Enriched.lean`*

## Part 10: Enriched Kan Extensions — Status and Roadmap

### Motivation

The bridge theorem (Part 4) identifies the stochastic Kan extension as
a concrete predicate `IsStochKanExtension` satisfying set-integral
factorization. Fritz [arXiv:1908.07021, §11] shows that this is an
*enriched* Kan extension in the **Stoch**-enriched sense, where the
weight is given by the conditional kernel and the colimit is computed
by integration.

Mathlib's `IsPointwiseLeftKanExtension` computes ordinary (Set-enriched)
Kan extensions via colimits in comma categories. This does **not** apply
to **Stoch** because:

1. The hom-objects in **Stoch** are spaces of kernels (not sets), and
   the colimit formula involves integration (not coproducts/coequalisers).
2. Ordinary colimits in **Stoch** are measure-theoretic sums, not the
   integration operation needed for conditional expectations.

### Mathlib Status (as of March 2026)

**Available:**
- `EnrichedCategory V C` — categories enriched over a monoidal category `V`
- `EnrichedFunctor` — functors between enriched categories
- `EnrichedOrdinaryCategory` — enriched categories with an underlying
  ordinary category
- `MonoidalClosed V` — closed monoidal categories (internal hom)
- Ends and coends (`end_`, `coend`) are partially formalised

**Available locally in this project (not upstream in Mathlib):**
- `CpmProofs.WeightedColimit` — a local weighted-colimit interface
  formalizing the representing-object definition used in enriched category theory
- `CpmProofs.EnrichedKanExtension` — a local pointwise enriched left
  Kan-extension interface built from weighted colimits
- `CpmProofs.EnrichedBridge` — a local specialization theorem showing
  that every kernel canonically determines the required weighted-cocone point,
  so the abstract weighted-colimit formula collapses to `lanValue` without any
  extra point-identification hypothesis
- `CpmProofs.StochSelfEnrichment` — candidate kernel-hom objects and
  abstract self-enrichment scaffolding, isolating the remaining stochastic gap

**Absent (blocking upstream / for the stochastic application):**
- **General enriched Kan extensions in Mathlib** — there is still no upstream
  API packaging these constructions as theorems and reusable infrastructure.
- **V-object of natural transformations** — marked TODO in Mathlib's
  enriched category files.
- **Monoidal structure on stochastic morphisms** — the current concrete category
  uses all kernels as morphisms, while the tensor and Markov-category laws are
  naturally phrased for Markov/s-finite kernels.
- **Kernel-space evaluation/curry-uncurry adjunction** — the project now has a
  candidate kernel-hom object, but not yet a genuine ordinary right adjoint:
  besides joint measurability, ordinary morphisms into that object are
  kernel-valued kernels, while the current curry construction only produces
  deterministic kernel-valued maps.

### What We Can State

With local weighted colimits and pointwise enriched Kan extensions in place,
but without stochastic self-enrichment, we can state the
*relationship* between our concrete `IsStochKanExtension` and the
would-be enriched version:

1. The `IsStochKanExtension` predicate (Part 4) is the
   measure-theoretic incarnation of the enriched colimit cocone.
2. The `ae_unique` theorem is the uniqueness of the mediating
   morphism (up to 2-cells = a.e. equalities).
3. The `lan_eq_integral_of_condKernel` factorization is the
   enriched cocone condition.
4. `EnrichedBridge.PointwiseEnrichedLeftKanExtension.weightedPointOfKernel`
   canonically converts a kernel `κ` into a point of the abstract weighted
   cocone object.
5. `EnrichedBridge.abstractLanValueOfKernelFromEnriched_eq_lanValue`
   shows that the abstract enriched pointwise formula for that canonical point
   is literally the concrete `lanValue`.
6. `EnrichedBridge.abstractLanValueOfKernelFromEnriched_isStochKanExtension`
   then lifts the same specialization to the universal property from Part 4.

### Results

| # | Result | Status |
|---|--------|--------|
| 34 | Enriched category instance for Meas (ordinary) | ✅ |
| 35 | Weighted colimit interface | ✅ (local) |
| 36 | Pointwise enriched left Kan extension interface | ✅ (local) |
| 37 | Candidate stochastic kernel-hom object | ✅ (local, partial) |
| 38 | Statement of remaining stochastic gap | ✅ (documented) |
| 39 | Canonical weighted-cocone point of a kernel | ✅ (local) |
| 40 | Abstract-to-concrete specialization theorem | ✅ (local, canonical in `κ`) |
| 41 | Specialized stochastic universal property | ✅ (local, canonical in `κ`) |
-/

open CategoryTheory MeasureTheory ProbabilityTheory

universe u v

namespace CpmProofs

/-!

### The Ordinary Category of Measurable Spaces

Mathlib's `EnrichedOrdinaryCategory` framework requires a `V`-enriched
category to also have an underlying ordinary category. For **Stoch**
(Part 1), the ordinary category is already defined: `Category MeasObj`
with kernels as morphisms.

The enrichment of **Stoch** over itself (self-enrichment) would require
`MonoidalClosed` on a category of measurable spaces with kernels. This
is a substantial construction that requires:

1. An internal hom `[X, Y]` — the measurable space of kernels from `X`
   to `Y`, equipped with a σ-algebra.
2. A tensor-hom adjunction: `Hom(X ⊗ Y, Z) ≅ Hom(X, [Y, Z])`.

For now, we record the available Mathlib infrastructure and the gap.
-/

/-- **Documentation theorem**: The enriched Kan extension formula.

In Fritz's framework, the stochastic left Kan extension of `G : A → X`
along `F : A → B` at `b : B` is:

```
(Lan_F G)(b) = ∫^{a:A} Stoch(Fa, b) ⊗ G(a)
```

where `⊗` is the "action" of **Stoch**-hom-objects on morphisms, and
the coend `∫^a` integrates over the fiber category.

In measure-theoretic terms, this reduces to:

```
(Lan_D f)(y) = ∫ f(x) dκ_y(x)
```

where `κ_y` is the conditional kernel — exactly our `lanValue` from Part 4.

The `IsStochKanExtension` predicate (Part 4) captures the universal
property: set-integral factorization with a.e. uniqueness. This is
the concrete incarnation of the enriched universal property.

**Current gap**: The project now contains local weighted-colimit and
pointwise enriched left Kan-extension definitions
(`CpmProofs.WeightedColimit` and
`CpmProofs.EnrichedKanExtension`), a bridge specialization theorem
that canonically constructs the relevant weighted-cocone point from a
kernel (`CpmProofs.EnrichedBridge`), and local self-enrichment
scaffolding (`CpmProofs.StochSelfEnrichment`). What is still
missing is a genuine stochastic `MonoidalClosed` structure: a monoidal
tensor on stochastic morphisms, joint measurability/evaluation data for
kernel-hom objects, and an ordinary right adjoint whose morphisms into
`[X, Z]` can represent more than deterministic kernel sections. In the
current ordinary category of all kernels, this last point is a genuine
design issue, not just unfinished proof plumbing. Once the correct
ambient stochastic category / internal-hom construction is supplied
(together with the concrete identification of the resulting pointwise
object with `Y`), the bridge theorem becomes a direct instance of the
general enriched Kan-extension formula. -/
theorem enriched_kan_is_condKernel_integration
    {X Y : MeasObj}
    (D : X → Y) (hD : Measurable D)
    (μ : Measure X)
    (κ : Kernel Y X)
    (_hκ : IsCondKernelMap D μ κ)
    (f : X → ℝ)
    (_hf_meas : AEStronglyMeasurable f μ)
    (_hf_int : Integrable f μ)
    (y : Y) :
    lanValue D hD κ f y = ∫ x, f x ∂(κ y) :=
  rfl

/-!

### Roadmap for the Full Enriched Kan Extension

The path to a fully enriched formalization now requires a combination of
local-to-upstream cleanup and stochastic enrichment work:

1. **Upstream weighted colimits and pointwise enriched Kan extensions**
   - Generalize the local `CpmProofs.WeightedColimit` and
     `CpmProofs.EnrichedKanExtension` interfaces
   - Connect them systematically to ends/coends and existence results
   - Add the corresponding Mathlib API for reuse outside this project

2. **General enriched Kan extensions** (`EnrichedLan F G`)
   - Package the pointwise construction functorially
   - Relate the weighted-colimit presentation to the coend formula

3. **Stoch self-enrichment** (`MonoidalClosed StochMarkov`)
   - Reuse the restricted monoidal category
     `CpmProofs.StochMarkov` now formalized in
     `CpmProofs.StochMarkov`
   - Promote the local candidate kernel-hom object
     `CpmProofs.kernelHomObj`
   - Prove the jointly measurable evaluation/curry-uncurry adjunction
   - Show `MarkovCategory StochMarkov` (Part 8)

4. **Bridge as enriched identity**
   - Instantiate the local canonical specialization in the stochastic setting
   - Show `IsStochKanExtension = IsEnrichedLeftKanExtension`
   - Derive `ae_unique` from the enriched universal property

Steps 1–2 are general enriched category theory (applicable beyond
probability). Steps 3–4 are specific to the stochastic setting.
The current formalization (Parts 1–5) provides the measure-theoretic
foundation that step 4 would connect to.
-/

end CpmProofs
