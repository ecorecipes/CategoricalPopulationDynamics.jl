import CpmProofs.CondKernel
import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
import Mathlib.MeasureTheory.Function.AEEqOfIntegral

/-!

*Source: `KanBridge.lean`*

## Part 4: The Bridge Theorem

This is the central result of the formalisation. The **bridge theorem**
connects two perspectives on conditional expectations:

### The Categorical View (Fritz §11)

Given a deterministic map `D : X → Y` and an observable `f : X → ℝ`,
the **pointwise left Kan extension** of `f` along `D` in the category
**Stoch** is a function `Lan_D f : Y → ℝ` that "best approximates" `f`
from the coarser space `Y`.

### The Measure-Theoretic View (Cho–Jacobs §4)

Given a conditional kernel `κ` for μ along `D`, the **conditional
expectation** of `f` given `D = y` is:

$$E[f \mid D = y] = \int_X f(x)\, \mathrm{d}\kappa_y(x)$$

### The Bridge

These two constructions are the same:

$$(\text{Lan}_D\, f)(y) = \int_X f(x)\, \mathrm{d}\kappa_y(x)$$

Moreover, the **factorization form** of the bridge gives:

$$\int_X f\, \mathrm{d}\mu = \int_Y (\text{Lan}_D\, f)(y)\, \mathrm{d}(D_*\mu)(y)$$

This identity is the one-variable disintegration formula, expressed in
the language of Kan extensions. It shows that the abstract categorical
construction (Kan extension) and the concrete measure-theoretic construction
(conditional kernel integration) agree — closing the Concrete Instantiation
Gap.

### Universal Property

We formalise the **stochastic Kan extension** as a concrete predicate
`IsStochKanExtension` (set-integral factorization) and prove:

1. `lanValue` satisfies the predicate (`lanValue_isStochKanExtension`)
2. Any two integrable solutions agree a.e. (`IsStochKanExtension.ae_unique`)

See the inline documentation for why Mathlib's
`IsPointwiseLeftKanExtension` (ordinary colimits) does not apply here.
-/

open CategoryTheory
open ProbabilityTheory
open MeasureTheory

universe u

namespace CpmProofs

/-- **Candidate pointwise value of the stochastic left Kan extension.**

For a conditional kernel `κ` along `D`, the Kan extension of an
observable `f : X → ℝ` at point `y : Y` is `∫ f dκ_y`.

This is the "integration against the conditional kernel" from
Fritz [arXiv:1908.07021, §11]. -/
noncomputable def lanValue
    {X Y : MeasObj}
    (D : X → Y) (_hD : Measurable D)
    (κ : Kernel Y X)
    (f : X → ℝ) : Y → ℝ :=
  fun y => ∫ x, f x ∂(κ y)

/-- **Bridge theorem (factorization form).**

If `κ` is a conditional kernel for `μ` along `D`, then `lanValue`
satisfies the integral factorization that characterizes the Kan extension:

$$\int_X f\, \mathrm{d}\mu = \int_Y (\text{lanValue}\ D\ \kappa\ f)(y)\, \mathrm{d}(D_*\mu)(y)$$

This is the core of the "Concrete Instantiation Gap": the pointwise
left Kan extension in **Stoch** equals integration against a conditional
kernel. The identity follows directly from the disintegration property
of conditional kernels (Fritz §11, Cho–Jacobs §4). -/
theorem lan_eq_integral_of_condKernel
    {X Y : MeasObj}
    (D : X → Y) (hD : Measurable D)
    (μ : Measure X)
    (κ : Kernel Y X)
    (hκ : IsCondKernelMap D μ κ)
    (f : X → ℝ)
    (hf_meas : AEStronglyMeasurable f μ)
    (hf_int : Integrable f μ) :
    (∫ x, f x ∂μ) = ∫ y, lanValue D hD κ f y ∂(Measure.map D μ) :=
  hκ.integral_factorization hf_meas hf_int

/-- **Bridge theorem (pointwise form).**

The Kan value at each point `y` is given by integration against the
conditional kernel `κ_y`. This is the defining equation of `lanValue` —
stated as a theorem for clarity that this is the key formula identified
by the bridge:

$$(\text{Lan}_D\, f)(y) = \int_X f(x)\, \mathrm{d}\kappa_y(x)$$

This equation says: "the best approximation of `f` from the coarser
space `Y` at point `y` is the expected value of `f` over the fiber
`D⁻¹(y)`, weighted by the conditional kernel." -/
theorem lanValue_eq_integral
    {X Y : MeasObj}
    (D : X → Y) (hD : Measurable D)
    (κ : Kernel Y X)
    (f : X → ℝ)
    (y : Y) :
    lanValue D hD κ f y = ∫ x, f x ∂(κ y) :=
  rfl

/-!

### The Universal Property of the Stochastic Kan Extension

#### Why not Mathlib's `IsPointwiseLeftKanExtension`?

Mathlib's `IsPointwiseLeftKanExtension` (in `Pointwise.lean`) computes
**ordinary categorical colimits** — coproducts over discrete comma
categories via `coconeAt`/`IsColimit`. This is appropriate for
Set-enriched categories, where colimits are computed pointwise from
coproducts and coequalisers.

The stochastic Kan extension requires **integration** — an enriched
weighted colimit where the weight is given by the conditional kernel.
This is fundamentally different: instead of a universal cone over a
discrete diagram, we have a measure-theoretic factorization through
an integral. In Fritz's framework (§11), this is a colimit in the
**Stoch**-enriched sense, which Mathlib's enriched category theory
does not yet cover.

#### Our approach: `IsStochKanExtension`

We define a concrete predicate `IsStochKanExtension` that captures
the correct universal property in measure-theoretic terms:

1. **Set-integral factorization**: for all measurable `B ⊆ Y`,
   $$\int_{D^{-1}(B)} f\, \mathrm{d}\mu
     = \int_B Lf(y)\, \mathrm{d}(D_*\mu)(y)$$

2. **Almost-everywhere uniqueness**: any two functions satisfying (1)
   agree `(D_*μ)`-a.e., via `Integrable.ae_eq_of_forall_setIntegral_eq`.

This is mathematically equivalent to the enriched Kan extension from
Fritz §11: the set-integral factorization is the enriched cocone
condition, and a.e. uniqueness is the universal property (uniqueness
of the mediating morphism up to the 2-cells of **Stoch**, which are
a.e. equalities).
-/

/-- **The stochastic Kan extension universal property.**

A function `Lf : Y → ℝ` is a stochastic left Kan extension of `f : X → ℝ`
along `D : X → Y` (with respect to measure μ) if it satisfies the
set-integral factorization:

$$\int_{D^{-1}(B)} f\, \mathrm{d}\mu
  = \int_B Lf(y)\, \mathrm{d}(D_*\mu)(y)$$

for every measurable `B ⊆ Y`. This is the measure-theoretic analogue of
the enriched weighted colimit from Fritz §11: the weight is the conditional
kernel, and the colimit cocone is given by integration.

The a.e. uniqueness of `Lf` (the universal property) is proved separately
in `IsStochKanExtension.ae_unique`. -/
structure IsStochKanExtension
    {X Y : Type u} [MeasurableSpace X] [MeasurableSpace Y]
    (D : X → Y) (μ : Measure X) (Lf : Y → ℝ) (f : X → ℝ) : Prop where
  /-- The coarsening map is measurable. -/
  measurable_D : Measurable D
  /-- Set-integral factorization: integrating `f` over `D⁻¹(B)` equals
  integrating `Lf` over `B` against the pushforward measure. -/
  setIntegral_factorization :
    ∀ ⦃B : Set Y⦄, MeasurableSet B →
      ∫ x in D ⁻¹' B, f x ∂μ = ∫ y in B, Lf y ∂(Measure.map D μ)

namespace IsStochKanExtension

variable {X Y : Type u} [MeasurableSpace X] [MeasurableSpace Y]
variable {D : X → Y} {μ : Measure X} {f : X → ℝ}

/-- **The global factorization**, derived from the set-integral version
by taking `B = Set.univ`. -/
theorem integral_factorization
    {Lf : Y → ℝ} (h : IsStochKanExtension D μ Lf f) :
    (∫ x, f x ∂μ) = ∫ y, Lf y ∂(Measure.map D μ) := by
  have := h.setIntegral_factorization MeasurableSet.univ
  simp [Set.preimage_univ] at this
  exact this

/-- **Almost-everywhere uniqueness of the stochastic Kan extension.**

If `Lf` and `Lg` both satisfy the set-integral factorization, and both
are integrable with respect to `D_*μ`, then they agree `(D_*μ)`-a.e.

This is the **universal property**: the stochastic Kan extension value
is unique up to a.e. equality — the appropriate notion of equality for
morphisms in **Stoch** (where 2-cells are a.e. equalities of densities).

The proof uses `Integrable.ae_eq_of_forall_setIntegral_eq` from Mathlib:
since both `Lf` and `Lg` have the same set integrals (against `D_*μ`)
over every measurable set, they must agree a.e. -/
theorem ae_unique
    {Lf Lg : Y → ℝ}
    (hLf : IsStochKanExtension D μ Lf f)
    (hLg : IsStochKanExtension D μ Lg f)
    (hLf_int : Integrable Lf (Measure.map D μ))
    (hLg_int : Integrable Lg (Measure.map D μ)) :
    Lf =ᵐ[Measure.map D μ] Lg := by
  apply Integrable.ae_eq_of_forall_setIntegral_eq _ _ hLf_int hLg_int
  intro B hB _
  rw [← hLf.setIntegral_factorization hB, ← hLg.setIntegral_factorization hB]

end IsStochKanExtension

/-- **The `lanValue` satisfies the stochastic Kan extension property.**

Given a conditional kernel `κ` for μ along `D`, the function
`lanValue D hD κ f` (i.e., `y ↦ ∫ f dκ_y`) satisfies the set-integral
factorization that defines the stochastic Kan extension. The proof
delegates directly to `IsCondKernelMap.setIntegral_disintegration`. -/
theorem lanValue_isStochKanExtension
    {X Y : MeasObj}
    (D : X → Y) (hD : Measurable D)
    (μ : Measure X)
    (κ : Kernel Y X)
    (hκ : IsCondKernelMap D μ κ)
    (f : X → ℝ)
    (hf_meas : AEStronglyMeasurable f μ)
    (hf_int : Integrable f μ) :
    IsStochKanExtension D μ (lanValue D hD κ f) f where
  measurable_D := hD
  setIntegral_factorization _B hB := hκ.setIntegral_disintegration hf_meas hf_int hB

/-- **The stochastic Kan extension of a conditional kernel.**

`lanValue D hD κ f` is a stochastic Kan extension of `f` along `D`,
meaning it satisfies the set-integral factorization and is unique up to
`(D_*μ)`-a.e. equality among integrable candidates.

See the module documentation for why Mathlib's
`IsPointwiseLeftKanExtension` does not apply here (ordinary vs enriched
colimits). -/
theorem isStochKanExtension_of_condKernel
    {X Y : MeasObj}
    (D : X → Y) (hD : Measurable D)
    (μ : Measure X)
    (κ : Kernel Y X)
    (hκ : IsCondKernelMap D μ κ)
    (f : X → ℝ)
    (hf_meas : AEStronglyMeasurable f μ)
    (hf_int : Integrable f μ) :
    IsStochKanExtension D μ (lanValue D hD κ f) f :=
  lanValue_isStochKanExtension D hD μ κ hκ f hf_meas hf_int

end CpmProofs
