import CpmProofs.Integration
import Mathlib.Probability.Kernel.Disintegration.Basic
import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import Mathlib.Probability.Kernel.Disintegration.Integral
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!

*Source: `CondKernel.lean`*

## Part 3: Conditional Kernels and Disintegration

A **conditional kernel** for a measure μ along a measurable map `D : X → Y`
is a kernel `κ : Kernel Y X` satisfying two properties:

1. **Fiber support**: for `(D_*μ)`-a.e. `y`, the measure `κ_y` is
   concentrated on the fiber `D⁻¹(y)`.
2. **Set-integral disintegration**: for all integrable `f` and measurable `B ⊆ Y`,
   $$\int_{D^{-1}(B)} f\, \mathrm{d}\mu = \int_B \left(\int_X f\, \mathrm{d}\kappa_y\right) \mathrm{d}(D_*\mu)(y)$$
   (taking `B = Y` recovers the global integral identity)

This is the **one-variable form** of disintegration, following Fritz
[arXiv:1908.07021, §11] and Cho–Jacobs [arXiv:1709.00322, §4].

### Why One-Variable Disintegration?

Mathlib's `Measure.condKernel` uses the stronger **product-space**
formulation, where disintegration is stated for the joint measure
`μ.map (fun x => (x, D x))` on `X × Y`. While mathematically equivalent,
the product-space version requires lifting measurability and integrability
conditions to the product space, which introduces technical overhead
orthogonal to the bridge theorem.

The one-variable form directly characterizes the "Kan extension value"
in the stochastic category: `∫ f dκ_y` is precisely the pointwise value
of the left Kan extension of `f` along `D` at `y`. This is the key
observation from Fritz §11 that we formalise in Part 4.
-/

open CategoryTheory
open ProbabilityTheory
open MeasureTheory
open Set

universe u

namespace CpmProofs

/-- A conditional kernel for a measure μ along a measurable map D.

This is an interface predicate capturing the two essential properties of
conditional kernels from Fritz §11 and Cho–Jacobs §4:

- `ae_mem_fiber`: κ_y is supported on D⁻¹(y) for (D_*μ)-a.e. y
- `setIntegral_disintegration`: set-integral disintegration for all measurable B ⊆ Y

The set-integral form enables the a.e.-uniqueness proof of the stochastic
Kan extension (Part 4). The global disintegration is derived as a corollary. -/
structure IsCondKernelMap
    {X Y : Type u} [MeasurableSpace X] [MeasurableSpace Y]
    (D : X → Y) (μ : Measure X) (κ : Kernel Y X) : Prop where
  measurable_D : Measurable D
  /-- Fiber support: for (D_*μ)-a.e. y, the kernel κ_y is supported on D⁻¹(y). -/
  ae_mem_fiber : ∀ᵐ y ∂(Measure.map D μ), ∀ᵐ x ∂(κ y), D x = y
  /-- Set-integral disintegration: ∫ x in D⁻¹(B), f dμ = ∫ y in B, (∫ f dκ_y) d(D_*μ)(y).

  This strengthens the global disintegration to hold over arbitrary measurable
  sets B ⊆ Y. Taking B = Set.univ recovers the global version.
  The set-integral form is needed for the a.e.-uniqueness proof of the
  stochastic Kan extension (Part 4), via
  `Integrable.ae_eq_of_forall_setIntegral_eq`. -/
  setIntegral_disintegration :
    ∀ ⦃f : X → ℝ⦄,
      AEStronglyMeasurable f μ →
      Integrable f μ →
      ∀ ⦃B : Set Y⦄, MeasurableSet B →
        ∫ x in D ⁻¹' B, f x ∂μ = ∫ y in B, (∫ x, f x ∂(κ y)) ∂(Measure.map D μ)

namespace IsCondKernelMap

variable {X Y : Type u} [MeasurableSpace X] [MeasurableSpace Y]
variable {D : X → Y} {μ : Measure X} {κ : Kernel Y X}

/-- **The set-integral factorization theorem.**

For any measurable set `B ⊆ Y`, integrating `f` over the preimage `D⁻¹(B)`
equals integrating the kernel expectations over `B`:

$$\int_{D^{-1}(B)} f\, \mathrm{d}\mu
  = \int_B \left(\int_X f\, \mathrm{d}\kappa_y\right) \mathrm{d}(D_*\mu)(y)$$

This is the local form of the disintegration identity. -/
theorem setIntegral_factorization
    (hκ : IsCondKernelMap D μ κ)
    {f : X → ℝ}
    (hf_meas : AEStronglyMeasurable f μ)
    (hf_int : Integrable f μ)
    {B : Set Y} (hB : MeasurableSet B) :
    ∫ x in D ⁻¹' B, f x ∂μ = ∫ y in B, (∫ x, f x ∂(κ y)) ∂(Measure.map D μ) :=
  hκ.setIntegral_disintegration hf_meas hf_int hB

/-- **The integral factorization theorem (global form).**

Integrating `f` against μ can be computed as an iterated integral through
the conditional kernel:

$$\int_X f\, \mathrm{d}\mu = \int_Y \left(\int_X f\, \mathrm{d}\kappa_y\right) \mathrm{d}(D_*\mu)(y)$$

This is the key identity underlying the "Concrete Instantiation Gap" bridge:
the pointwise left Kan extension of `f` along `D` in **Stoch** equals
integration against the conditional kernel κ. Derived from the stronger
`setIntegral_disintegration` by taking `B = Set.univ`. -/
theorem integral_factorization
    (hκ : IsCondKernelMap D μ κ)
    {f : X → ℝ}
    (hf_meas : AEStronglyMeasurable f μ)
    (hf_int : Integrable f μ) :
    (∫ x, f x ∂μ) = ∫ y, ∫ x, f x ∂(κ y) ∂(Measure.map D μ) := by
  have h := hκ.setIntegral_disintegration hf_meas hf_int MeasurableSet.univ
  simp [Set.preimage_univ] at h
  exact h

end IsCondKernelMap

/-!

### Constructing `IsCondKernelMap` from Mathlib's `Measure.condKernel`

Given a measurable map `D : X → Y` and a finite measure `μ` on `X`,
we form the joint measure `ρ := μ.map (fun x => (D x, x))` on `Y × X`.
Mathlib's `ρ.condKernel : Kernel Y X` then satisfies our one-variable
disintegration interface `IsCondKernelMap`.

**Proof outline.**

1. `ρ.fst = D_*μ`: Since `ρ = μ.map g` where `g x = (D x, x)`, we have
   `ρ.fst = (μ.map g).map Prod.fst = μ.map (Prod.fst ∘ g) = μ.map D`.

2. **Fiber support**: `ρ` is concentrated on `{(y,x) | y = D x}` (being
   the pushforward of the graph embedding `x ↦ (D x, x)`). By Mathlib's
   disintegration (`lintegral_condKernel_mem`), this zero-mass condition
   transfers: for `ρ.fst`-a.e. `y`, we have `ρ.condKernel y`-a.e. `D x = y`.

3. **Set-integral disintegration**: Chaining `integral_map` with
   `setIntegral_condKernel_univ_right`:
   ```
   ∫ x in D⁻¹'B, f x ∂μ
     = ∫ p in B ×ˢ univ, (f ∘ Prod.snd) p ∂ρ
     = ∫ y in B, ∫ x, f x ∂(ρ.condKernel y) ∂ρ.fst
     = ∫ y in B, ∫ x, f x ∂(ρ.condKernel y) ∂(D_*μ)
   ```
-/

/-- The graph embedding `x ↦ (D x, x)` is measurable. -/
private theorem measurable_graph {X Y : Type u}
    [MeasurableSpace X] [MeasurableSpace Y]
    {D : X → Y} (hD : Measurable D) :
    Measurable (fun x => (D x, x)) :=
  Measurable.prod hD measurable_id

/-- `ρ.fst = D_*μ` where `ρ := μ.map (fun x => (D x, x))`.
This identification is needed to rewrite the base measure in the
disintegration from `ρ.fst` to `D_*μ`. -/
private theorem fst_graph_eq_map {X Y : Type u}
    [MeasurableSpace X] [MeasurableSpace Y]
    {D : X → Y} (hD : Measurable D)
    (μ : Measure X) :
    (μ.map (fun x => (D x, x))).fst = Measure.map D μ := by
  show (μ.map (fun x => (D x, x))).map Prod.fst = μ.map D
  rw [Measure.map_map measurable_fst (Measurable.prod hD measurable_id)]
  simp only [Function.comp_def]

/-- The graph embedding `x ↦ (D x, x)` is a measurable embedding.

This requires `MeasurableEq Y` to ensure the graph (range of the
embedding) is a measurable set: `{p : Y × X | p.1 = D p.2}` is
measurable by `measurableSet_eq_fun`. -/
private theorem measurableEmbedding_graph {X Y : Type u}
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableEq Y]
    {D : X → Y} (hD : Measurable D) :
    MeasurableEmbedding (fun x => (D x, x)) where
  injective := fun _ _ h => congr_arg Prod.snd h
  measurable := Measurable.prod hD measurable_id
  measurableSet_image' := by
    intro s hs
    -- g '' s = {p | p.2 ∈ s} ∩ {p | p.1 = D p.2}
    have h1 : MeasurableSet (Prod.snd ⁻¹' s : Set (Y × X)) := measurable_snd hs
    have h2 : MeasurableSet ({p : Y × X | p.1 = D p.2}) :=
      measurableSet_eq_fun measurable_fst (hD.comp measurable_snd)
    convert h1.inter h2 using 1
    ext ⟨y, x⟩
    simp only [Set.mem_image, Prod.mk.injEq, Set.mem_inter_iff, Set.mem_preimage,
      Set.mem_setOf_eq]
    exact ⟨fun ⟨a, ha, h1, h2⟩ => by subst h2; exact ⟨ha, h1.symm⟩,
           fun ⟨hx, h⟩ => ⟨x, hx, h.symm, rfl⟩⟩

/-- **`Measure.condKernel` yields an `IsCondKernelMap` instance.**

Given a measurable map `D : X → Y` and a finite measure `μ` on a
standard Borel space `X`, the conditional kernel of the joint measure
`ρ := μ.map (fun x => (D x, x))` satisfies the one-variable
disintegration interface `IsCondKernelMap D μ`.

This bridges the gap between Mathlib's product-space formulation of
disintegration and the one-variable formulation used in the bridge theorem.
The product-space overhead is absorbed here, so downstream code can work
entirely with the simpler `IsCondKernelMap` interface. -/
theorem condKernel_isCondKernelMap
    {X Y : Type u}
    [MeasurableSpace X] [StandardBorelSpace X] [Nonempty X]
    [MeasurableSpace Y] [MeasurableEq Y]
    (D : X → Y) (hD : Measurable D)
    (μ : Measure X) [IsFiniteMeasure μ] :
    IsCondKernelMap D μ ((μ.map (fun x => (D x, x))).condKernel) where
  measurable_D := hD
  ae_mem_fiber := by
    -- ρ is concentrated on {(y,x) | y = D x} since it is the pushforward
    -- of the graph embedding x ↦ (D x, x). By disintegration, this transfers
    -- to the conditional kernel: for ρ.fst-a.e. y, κ_y is supported on {x | D x = y}.
    -- Since ρ.fst = D_*μ, this gives the result.
    set ρ := μ.map (fun x => (D x, x))
    rw [← fst_graph_eq_map hD μ]
    -- The "bad" set: points not on the graph
    set s : Set (Y × X) := {p | D p.2 ≠ p.1}
    -- s is measurable (complement of the graph)
    have hs_meas : MeasurableSet s :=
      (measurableSet_eq_fun (hD.comp measurable_snd) measurable_fst).compl
    -- ρ(s) = 0 since ρ is the pushforward of the graph embedding
    have hρs : ρ s = 0 := by
      rw [Measure.map_apply (measurable_graph hD) hs_meas]
      have : (fun x => (D x, x)) ⁻¹' s = ∅ := by ext x; simp [s]
      rw [this, measure_empty]
    -- By disintegration: ∫⁻ y, condKernel_y({x | D x ≠ y}) d(ρ.fst)(y) = ρ(s) = 0
    have hlint : ∫⁻ y, ρ.condKernel y (Prod.mk y ⁻¹' s) ∂ρ.fst = 0 := by
      change ∫⁻ y, ρ.condKernel y {x | (y, x) ∈ s} ∂ρ.fst = 0
      exact (Measure.lintegral_condKernel_mem hs_meas).trans hρs
    -- The integrand is 0 a.e.
    have hae : ∀ᵐ y ∂ρ.fst, ρ.condKernel y (Prod.mk y ⁻¹' s) = 0 := by
      rwa [lintegral_eq_zero_iff
        (Kernel.measurable_kernel_prodMk_left hs_meas)] at hlint
    -- Convert: condKernel_y({x | D x ≠ y}) = 0  →  ∀ᵐ x, D x = y
    filter_upwards [hae] with y hy
    -- Prod.mk y ⁻¹' s = {x | ¬(D x = y)} since s = {p | D p.2 ≠ p.1}
    change (ρ.condKernel y) {x | ¬(D x = y)} = 0 at hy
    exact ae_iff.mpr hy
  setIntegral_disintegration := by
    intro f hf_meas hf_int B hB
    -- The proof chains MeasurableEmbedding.setIntegral_map (to pass from μ to ρ)
    -- with setIntegral_condKernel_univ_right (Mathlib's disintegration on the
    -- product space), then substitutes ρ.fst = D_*μ.
    set ρ := μ.map (fun x => (D x, x)) with hρ_def
    have hg_emb : MeasurableEmbedding (fun x => (D x, x)) := measurableEmbedding_graph hD
    -- Step 1: ∫ x in D⁻¹'B, f x ∂μ = ∫ p in B ×ˢ univ, f p.2 ∂ρ
    have hset : (fun x => (D x, x)) ⁻¹' (B ×ˢ Set.univ) = D ⁻¹' B := by
      ext x; simp [Set.mem_prod, Set.mem_preimage]
    have step1 : ∫ x in D ⁻¹' B, f x ∂μ = ∫ p in B ×ˢ Set.univ, f p.2 ∂ρ := by
      have h := hg_emb.setIntegral_map (μ := μ) (fun p : Y × X => f p.2) (B ×ˢ Set.univ)
      simp only [← hρ_def] at h
      rw [hset] at h; exact h.symm
    -- IntegrableOn condition for Step 2
    have hfi : IntegrableOn (fun p : Y × X => f p.2) (B ×ˢ Set.univ) ρ := by
      rw [hg_emb.integrableOn_map_iff]
      show IntegrableOn ((fun p : Y × X => f p.2) ∘ (fun x => (D x, x)))
        ((fun x => (D x, x)) ⁻¹' (B ×ˢ Set.univ)) μ
      simp only [Function.comp_def, hset]
      exact hf_int.integrableOn
    -- Step 2: ∫ p in B ×ˢ univ, f p.2 ∂ρ = ∫ y in B, ∫ x, f x ∂(ρ.condKernel y) ∂ρ.fst
    have step2 : ∫ p in B ×ˢ Set.univ, f p.2 ∂ρ =
        ∫ y in B, ∫ x, f x ∂(ρ.condKernel y) ∂ρ.fst :=
      (Measure.setIntegral_condKernel_univ_right hB hfi).symm
    -- Step 3: Rewrite ρ.fst = D_*μ
    rw [step1, step2, fst_graph_eq_map hD μ]

end CpmProofs
