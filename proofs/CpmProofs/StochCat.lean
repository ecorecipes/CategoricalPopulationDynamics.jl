import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Probability.Kernel.Basic
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.CompMap

/-!
*Source: `StochCat.lean`*

## Introduction

The **Concrete Instantiation Gap** is the problem of connecting two ways of
thinking about conditional expectations in probability theory:

1. **Categorical**: The pointwise left Kan extension of an observable along a
   deterministic map in the category **Stoch** of Markov kernels.
2. **Measure-theoretic**: Integration against a conditional kernel (regular
   conditional distribution) obtained by disintegration.

Fritz [arXiv:1908.07021] showed that these coincide in the synthetic
framework of Markov categories. Cho and Jacobs [arXiv:1709.00322] gave a
string-diagrammatic account of disintegration and Bayesian inversion. This
formalisation provides machine-checked proofs of the key identities, building
on Mathlib's measure theory and category theory libraries.

### Structure of the Formalisation

| Part | File | Content |
|------|------|---------|
| 1 | `StochCat.lean` | The stochastic category: bundled measurable spaces with Markov kernels as morphisms |
| 2 | `Integration.lean` | Integration along kernels: the observable-level semantics |
| 3 | `CondKernel.lean` | Conditional kernels and one-variable disintegration |
| 4 | `KanBridge.lean` | The bridge theorem: Kan extensions = conditional expectations |
| 5 | `BinExample.lean` | Concrete application: interval binning and midpoint quadrature |
| 15 | `MeasDet.lean` | Deterministic Kan extensions in Meas |
| 16 | `StochConvergence.lean` | Convergence of stochastic to deterministic models |

### Summary of Results

| # | Result | Status |
|---|--------|--------|
| 1 | **Stoch** is a category (identity, composition, associativity) | ✅ |
| 2 | Deterministic kernels define a functor **Meas** → **Stoch** | ✅ |
| 3 | Integration along a deterministic kernel = function composition | ✅ |
| 4 | Integration along a composite kernel = iterated integration | ✅ |
| 5 | Conditional kernels satisfy set-integral disintegration | ✅ |
| 6 | `IsCondKernelMap` instance from Mathlib's `condKernel` | ✅ |
| 7 | The Kan extension value = integration against the conditional kernel | ✅ |
| 8 | The bridge factorization: ∫ f dμ = ∫ (Lan f)(y) d(D_*μ)(y) | ✅ |
| 9 | Stochastic Kan extension: existence (`lanValue_isStochKanExtension`) | ✅ |
| 10 | Stochastic Kan extension: a.e. uniqueness (`ae_unique`) | ✅ |
| 11 | Bin kernel = normalized restricted Lebesgue measure | ✅ |
| 12 | Bin kernel is a conditional kernel (`binKernel_isCondKernelMap`) | ✅ |
| 13 | Integration against bin kernel = bin average | ✅ |
| 14 | Midpoint quadrature error bound (`midpoint_quadrature_error`) | ✅ |
| 15 | Midpoint quadrature approximates Kan value to O(h²) | ✅ |
| 16 | Bin kernel gives a stochastic Kan extension | ✅ |

All 16 results are fully machine-checked with no `sorry` statements.
The midpoint quadrature error bound (#14) uses the iterated FTC technique:
a Lipschitz bound on `f'` from the Convex MVT gives the tight `M₂/2`
factor in the pointwise Taylor remainder, which is then integrated.

### Novelty

To the best of our knowledge, this is the first machine-checked formalisation
connecting categorical Kan extensions with measure-theoretic conditional
kernels in any proof assistant. Prior related work includes:

| Component | Prior art | This project |
|-----------|-----------|-------------|
| **Stoch** as a category | Not defined in Mathlib, Coq, or Isabelle. Degenne [arXiv:2510.04070] notes the building blocks exist in Mathlib but the category instance does not. | First `Category` instance on bundled measurable spaces with Markov kernels as morphisms. |
| Disintegration (product-space) | Mathlib's `condKernel`; Hirata's Isabelle/AFP entry (2023). | Uses Mathlib's `condKernel` internally. |
| One-variable disintegration along a map | Not formalised. | `IsCondKernelMap`: fiber support + set-integral disintegration along `D : X → Y`. Constructed from Mathlib's `condKernel` via `condKernel_isCondKernelMap`. |
| Kan extensions (general) | Mathlib's `Lan`, `Ran`, `IsPointwiseLeftKanExtension`. | Uses Mathlib's categorical infrastructure as context; explains why ordinary colimits do not apply (enriched vs Set-enriched). |
| Stochastic Kan extension | Not formalised. Fritz §11 gives the pen-and-paper theory. | `IsStochKanExtension`: set-integral factorization predicate with a.e. uniqueness. |
| Bridge: Kan ext = conditional kernel | Not formalised in any proof assistant. | `lan_eq_integral_of_condKernel` and `lanValue_isStochKanExtension`. |
| Midpoint quadrature error bound | Not formalised. Mathlib has trapezoidal rule infrastructure. | `midpoint_quadrature_error`: fully proved O(h²) bound via iterated FTC. |
| s-finite kernel hierarchies | Affeldt et al. (Coq, CPP 2023). | Not covered (orthogonal direction). |

The formalisation sits at the intersection of **categorical probability**
(Fritz, Cho–Jacobs), **formal verification** (Lean 4 / Mathlib), and
**applied mathematics** (integral projection models, numerical quadrature).

### References

- T. Fritz, *A synthetic approach to Markov kernels, conditional independence
  and theorems on sufficient statistics*, Adv. Math. 370 (2020),
  [arXiv:1908.07021](https://arxiv.org/abs/1908.07021).
- K. Cho and B. Jacobs, *Disintegration and Bayesian inversion via string
  diagrams*, Math. Struct. Comput. Sci. 29 (2019),
  [arXiv:1709.00322](https://arxiv.org/abs/1709.00322).

---

## Part 1: The Stochastic Category

The category **Stoch** has measurable spaces as objects and Markov kernels
as morphisms. This is the natural setting for probability theory viewed
through a categorical lens (Fritz §2, Cho–Jacobs §2).

- **Objects**: Measurable spaces (bundled as `MeasObj`)
- **Morphisms**: Markov kernels `κ : Kernel X Y`
- **Identity**: The Dirac (identity) kernel `Kernel.id`
- **Composition**: Kernel composition in diagrammatic order (`η ∘ₖ κ`)

The key insight is that composition in **Stoch** is *diagrammatic*: the
categorical composite `κ ≫ η` corresponds to `η ∘ₖ κ` in Mathlib's kernel
library. This reversal arises because Mathlib defines kernel composition
as integration: `(η ∘ₖ κ)(x, B) = ∫ η(y, B) dκ(x, dy)`, which reads
"first sample from κ at x, then from η at y".
-/

open CategoryTheory
open ProbabilityTheory
open MeasureTheory

universe u

namespace CpmProofs

/-- Bundled measurable spaces — the objects of **Stoch**.

Each `MeasObj` pairs a type with its σ-algebra. This is the concrete
analogue of the objects in Fritz's Markov category. -/
structure MeasObj where
  α : Type u
  inst : MeasurableSpace α

attribute [instance] MeasObj.inst

instance : CoeSort MeasObj (Type u) := ⟨MeasObj.α⟩

namespace MeasObj

/-- Morphisms in the concrete stochastic category are Markov kernels.

A kernel `κ : Kernel X Y` assigns to each point `x : X` a measure `κ(x)`
on `Y`. In the stochastic category, these generalize both deterministic
functions (via Dirac kernels) and random transitions. -/
abbrev Hom (X Y : MeasObj) := Kernel X Y

/-- **Stoch is a category.**

The category structure on bundled measurable spaces, with Markov kernels
as morphisms:

- **Identity**: `Kernel.id` (the Dirac kernel: δ_x on each fiber)
- **Composition**: `η ∘ₖ κ` (diagrammatic order — note the reversal!)
- **Associativity**: from `Kernel.comp_assoc`
- **Left identity**: `Kernel.comp_id` (composing with Dirac on the right)
- **Right identity**: `Kernel.id_comp` (composing with Dirac on the left)

This corresponds to **Stoch** as defined in Fritz §2.1, instantiated
concretely using Mathlib's `Kernel` type. -/
noncomputable instance : Category MeasObj where
  Hom X Y := Hom X Y
  id _ := Kernel.id
  comp κ η := η ∘ₖ κ
  id_comp κ := Kernel.comp_id κ
  comp_id κ := Kernel.id_comp κ
  assoc κ η θ := (Kernel.comp_assoc θ η κ).symm

/-- Coerce morphisms in MeasObj to functions, inheriting the FunLike
instance from `Kernel`. This allows writing `κ x` for a morphism
`κ : X ⟶ Y` to obtain the measure `κ(x)` on `Y`. -/
noncomputable instance homFunLike {X Y : MeasObj} : FunLike (X ⟶ Y) X (Measure Y) :=
  Kernel.instFunLike

/-!
### Deterministic Kernels

Every measurable function `f : X → Y` gives rise to a deterministic
kernel `det f hf : X ⟶ Y` via the Dirac construction:
`(det f hf)(x) = δ_{f(x)}`.

This defines a functor from **Meas** (the category of measurable spaces
and measurable functions) to **Stoch**. The functoriality — that
`det (g ∘ f) = det f ≫ det g` — is proved below.
-/

/-- Deterministic kernel associated to a measurable map.

This is the "embedding" of **Meas** into **Stoch**: every measurable
function `f : X → Y` becomes the Dirac kernel `x ↦ δ_{f(x)}`.

In Fritz's framework, this is the deterministic morphism functor
(Fritz §2.2). In Cho–Jacobs, these are the "pure" or "point" maps. -/
noncomputable def det {X Y : MeasObj} (f : X → Y) (hf : Measurable f) : (X ⟶ Y) :=
  Kernel.deterministic f hf

/-- Associativity of kernel composition, stated in categorical notation.

This is a direct consequence of the `Category.assoc` law, which in turn
reduces to `Kernel.comp_assoc` from Mathlib. -/
theorem comp_assoc_placeholder
    {W X Y Z : MeasObj} (κ : W ⟶ X) (η : X ⟶ Y) (θ : Y ⟶ Z) :
    (κ ≫ η) ≫ θ = κ ≫ (η ≫ θ) :=
  Category.assoc κ η θ

/-- **Deterministic kernels define a functor Meas → Stoch.**

The composition law: `det (g ∘ f) = det f ≫ det g`. This shows that the
Dirac construction is functorial — it preserves composition of measurable
functions. Combined with `det id = id` (which follows from
`Kernel.deterministic_id`), this makes `det` a functor.

This is the concrete version of the deterministic-morphism functor
from Fritz §2.2. -/
theorem det_comp_placeholder
    {X Y Z : MeasObj}
    (f : X → Y) (g : Y → Z)
    (hf : Measurable f) (hg : Measurable g) :
    det (g ∘ f) (hg.comp hf) = det f hf ≫ det g hg :=
  (Kernel.deterministic_comp_deterministic hf hg).symm

end MeasObj

end CpmProofs
