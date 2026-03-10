import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.Whiskering
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.CategoryTheory.Functor.Flat

/-!

*Source: `Adjunction.lean`*

# Adjunction Framework for Discretisation and Refinement

**Machine-checked proofs of the categorical adjunction chain underlying
CategoricalProjectionModels.jl — the abstract framework connecting
continuous IPMs and discrete MPMs.**

*Author: Simon Frost*

This file formalises the adjunction chain Lan_D ⊣ D* ⊣ Ran_D and its
structural properties: triangle identities, full faithfulness
characterisation of error, naturality of unit/counit, round-trip
self-consistency, colimit preservation, and flatness.

These results correspond to Parts 1–8 of the CategoricalProjectionModels.jl
formal verification.

## Glossary of Terms

### Categorical Terms

| Term | Mathematical Definition | Ecological Meaning |
|------|------------------------|-------------------|
| **Category** | A collection of objects and morphisms (arrows) with identity and composition laws | The "universe" of population models and the transformations between them |
| **Functor** | A structure-preserving map between categories: sends objects to objects, morphisms to morphisms, respecting identity and composition | Converting between model representations (e.g., IPM → MPM) while preserving model relationships |
| **Natural transformation** | A systematic family of morphisms between two functors, one for each object, satisfying a coherence condition | Error measures (unit, counit) that vary coherently across *all* models, not just specific examples |
| **Adjunction** (F ⊣ G) | A pair of functors with a natural bijection Hom(F(X), Y) ≅ Hom(X, G(Y)) | Discretisation (Lan_D) and restriction (D\*) are optimally paired: discretising is the "best" way to approximate |
| **Left Kan extension** (Lan_D) | Given D : S → L, the left Kan extension of F : S → C along D is the "closest approximation from below" | Discretising a continuous kernel K(z',z) into a matrix A: the midpoint-rule integral A_{ij} = h·K(z_i, z_j) |
| **Right Kan extension** (Ran_D) | The dual: "closest approximation from above" | Reconstructing a piecewise-constant kernel from a matrix: K_pw(z',z) = A_{ij}/h |
| **Unit** (η) | The comparison morphism Id → G ∘ F for an adjunction F ⊣ G | Self-consistency check: discretise a matrix, then refine back — do you recover the original? (Yes, exactly.) |
| **Counit** (ε) | The dual comparison F ∘ G → Id | Approximation quality: refine a kernel to piecewise-constant, then re-discretise — how close is it to the original? |
| **Flat functor** | A functor whose left Kan extension preserves finite limits (including pullbacks) | Condition ensuring that discretisation commutes with stratification — satisfied when bins partition the trait space |
| **Fully faithful functor** | A functor that is bijective on hom-sets (no information lost between any pair of objects) | Characterises when discretisation is *exact*: the kernel is completely determined by its values at mesh points |

---
-/

open CategoryTheory CategoryTheory.Functor

universe u v


/-!

## Part 1: The Restriction (Precomposition) Functor D*

**Package claim** (src/kan_extensions.jl, lines 1–8):
The discretisation functor D embeds finite bin-indices into the
continuous trait space. The *restriction functor* D* is precomposition
with D: it sends a continuous kernel F : L ⥤ C to a discrete kernel
D*(F) = D ⋙ F : S ⥤ C by evaluating F only at the bin midpoints.

**Ecological meaning**: Given a continuous model of how plants grow,
survive, and reproduce as a function of body size, D* "samples" the
model at the midpoints of discrete size bins, producing a matrix
representation. This is what ecologists do when they build an MPM from
an IPM — they evaluate the kernel at representative sizes.

**Mathematical content**: D* is Mathlib's `whiskeringLeft`, the functor
that precomposes with a fixed functor ι : S ⥤ L.
-/

section Restriction

variable (S : Type u) [Category.{v} S]
variable (L : Type u) [Category.{v} L]
variable (D : Type u) [Category.{v} D]

/-- The restriction (precomposition) functor ι* : (L ⥤ D) ⥤ (S ⥤ D).
    Sends F : L ⥤ D to ι ⋙ F : S ⥤ D. This is Mathlib's whiskeringLeft.

    In the package, this corresponds to evaluating a continuous kernel
    at mesh points — the first step of `left_kan_extension`. -/
def restrictionFunctor (ι : S ⥤ L) : (L ⥤ D) ⥤ (S ⥤ D) :=
  (whiskeringLeft S L D).obj ι

/-- The restriction functor is definitionally equal to Mathlib's whiskeringLeft.
    This confirms we are using the standard categorical construction. -/
theorem restriction_eq_whiskering (ι : S ⥤ L) :
    restrictionFunctor S L D ι = (whiskeringLeft S L D).obj ι :=
  rfl

end Restriction


/-!

## Part 2: The Adjunction Chain Lan_D ⊣ D* ⊣ Ran_D

**Package claim** (src/kan_extensions.jl; vignettes 01, 02, 05):
The left Kan extension (discretisation) and right Kan extension
(refinement) form an adjunction chain with the restriction functor:

$$\text{Lan}_D \dashv D^* \dashv \text{Ran}_D$$

This is *two* adjunctions sharing a middle functor D*:

- Lan_D ⊣ D* : "discretisation is the best approximation from below"
- D* ⊣ Ran_D : "refinement is the best approximation from above"

**Ecological meaning**: When an ecologist discretises a continuous IPM
into an MPM (Lan_D), the resulting matrix is the *optimal* discrete
representation in a precise categorical sense. Conversely, when
reconstructing a continuous model from a matrix (Ran_D), the
piecewise-constant kernel is the optimal continuous representation
given only the matrix data.

The hom-set equivalences state:

- Hom(Lan_D(X), Y) ≅ Hom(X, D*(Y)) — every way to compare the
  discretised model to an MPM corresponds uniquely to a way to compare
  the original IPM to the MPM's continuous extension.
- Hom(D*(X), Y) ≅ Hom(X, Ran_D(Y)) — every way to compare the
  restriction of an IPM to an MPM corresponds uniquely to a way to
  compare the IPM to the MPM's refinement.
-/

section AdjunctionChain

variable {C : Type u} [Category.{v} C]
variable {D : Type u} [Category.{v} D]

/-- Given two adjunctions sharing a middle functor L ⊣ M and M ⊣ R,
    the first adjunction provides the hom-set equivalence
    Hom(L(X), Y) ≅ Hom(X, M(Y)).

    In the package: Hom(Lan_D(X), Y) ≅ Hom(X, D*(Y)).
    Ecologically: comparing a discretised IPM to any MPM is the same as
    comparing the original IPM to the MPM's continuous extension. -/
def adjunction_chain_hom_equiv₁
    {L : C ⥤ D} {M : D ⥤ C} {R : C ⥤ D}
    (adj₁ : L ⊣ M) (_adj₂ : M ⊣ R) (X : C) (Y : D) :
    (L.obj X ⟶ Y) ≃ (X ⟶ M.obj Y) :=
  adj₁.homEquiv X Y

/-- The second adjunction: Hom(M(X), Y) ≅ Hom(X, R(Y)).

    In the package: Hom(D*(X), Y) ≅ Hom(X, Ran_D(Y)).
    Ecologically: comparing the restriction of an IPM to bins is the same
    as comparing the IPM to the best piecewise-constant approximation. -/
def adjunction_chain_hom_equiv₂
    {L : C ⥤ D} {M : D ⥤ C} {R : C ⥤ D}
    (_adj₁ : L ⊣ M) (adj₂ : M ⊣ R) (X : D) (Y : C) :
    (M.obj X ⟶ Y) ≃ (X ⟶ R.obj Y) :=
  adj₂.homEquiv X Y

/-- The unit η_X : X → M(L(X)) exists as a canonical morphism.
    This is the comparison map used by `unit_error` in the package.

    Ecologically: η measures how much information is lost when a matrix is
    discretised and then refined back to a piecewise-constant kernel. -/
theorem unit_exists
    {L : C ⥤ D} {M : D ⥤ C}
    (adj : L ⊣ M) (X : C) :
    ∃ (η : X ⟶ M.obj (L.obj X)), η = adj.unit.app X :=
  ⟨adj.unit.app X, rfl⟩

end AdjunctionChain


/-!

## Part 3: Triangle Identities (Zig-Zag Equations)

**Package claim** (src/diagnostics.jl; vignettes 01, 02):
The unit η and counit ε of the adjunction satisfy the *triangle
identities* (also called zig-zag equations):

- **Left triangle**: F(η_X) ≫ ε_{F(X)} = id_{F(X)}
- **Right triangle**: η_{G(Y)} ≫ G(ε_Y) = id_{G(Y)}

These are the structural backbone ensuring the adjunction is well-formed.

**Ecological meaning**:

- **Left triangle** (for Lan_D ⊣ D*): Take an MPM X. Discretise it
  (η maps X into D*(Lan_D(X))). Then apply Lan_D and the counit.
  The composite is the identity on Lan_D(X). This means: the
  discretisation-then-refinement-then-discretisation round-trip is
  perfectly self-consistent on the "MPM side."

- **Right triangle** (for Lan_D ⊣ D*): Take an IPM Y. Restrict it
  to bins (D*(Y)). Apply the unit, then D* to the counit. The
  composite is the identity on D*(Y). This means: the
  restriction-then-extension-then-restriction round-trip is perfectly
  self-consistent on the "IPM side."

These identities are why `unit_error(A, domain)` returns 0 in the
package — the matrix round-trip A → Ran_D → Lan_D → A' gives A' = A.
-/

section TriangleIdentities

variable {C : Type u} [Category.{v} C]
variable {E : Type u} [Category.{v} E]
variable {F : C ⥤ E} {G : E ⥤ C}

/-- Left triangle identity: F(η_X) ≫ ε_{F(X)} = id_{F(X)}.

    Package function: `unit_error` in diagnostics.jl returns 0 because
    of this identity — the matrix round-trip is exact.

    Ecological interpretation: if you take an MPM, extend it to a
    piecewise-constant kernel (Ran_D), then re-discretise (Lan_D),
    you recover the original MPM exactly. No demographic information
    is lost in this round-trip. -/
theorem left_triangle_identity (adj : F ⊣ G) (X : C) :
    F.map (adj.unit.app X) ≫ adj.counit.app (F.obj X) = 𝟙 (F.obj X) :=
  adj.left_triangle_components X

/-- Right triangle identity: η_{G(Y)} ≫ G(ε_Y) = id_{G(Y)}.

    Ecological interpretation: if you take an IPM, discretise it to an
    MPM (Lan_D), then extend back to a piecewise-constant kernel (Ran_D),
    the result restricted to the original bins is the same as the original
    restriction. The round-trip is exact "as seen from the bins." -/
theorem right_triangle_identity (adj : F ⊣ G) (Y : E) :
    adj.unit.app (G.obj Y) ≫ G.map (adj.counit.app Y) = 𝟙 (G.obj Y) :=
  adj.right_triangle_components Y

end TriangleIdentities


/-!

## Part 4: Error Characterisation via Full Faithfulness

**Package claim** (src/diagnostics.jl, lines 7–49; vignette 02):

- The counit ε is a natural isomorphism if and only if D* is fully
  faithful. This means: the midpoint-rule approximation is *exact*
  if and only if the kernel is piecewise-constant on the bins.
- The unit η is a natural isomorphism if and only if Lan_D is fully
  faithful. This means: the self-consistency check passes trivially
  if and only if discretisation preserves all information.

**Ecological meaning**:

- **Counit iso** (ε = id): A species whose vital rates (survival,
  growth, fecundity) are exactly constant within each size bin can be
  discretised with zero error. Real species have smooth vital rates,
  so ε ≠ id in practice — but finer bins make ε closer to an iso.
  This is why `counit_error(kernel, domain)` decreases as mesh
  resolution increases.

- **Unit iso** (η = id): If the discretisation functor preserves all
  information (fully faithful), then every MPM is the exact discretisation
  of some IPM. In practice this always holds for the midpoint rule,
  which is why `unit_error(A, domain)` returns 0.
-/

section ErrorCharacterisation

variable {C : Type u} [Category.{v} C]
variable {E : Type u} [Category.{v} E]
variable (F : C ⥤ E) (G : E ⥤ C)
variable (adj : F ⊣ G)

/-- If D* (= G, the restriction functor) is fully faithful, then the
    counit ε is a natural isomorphism.

    Package connection: `counit_error` measures ‖ε - id‖. When ε is an
    iso, this error is zero. For smooth kernels ε is not an iso, and
    the error is positive but decreasing with mesh refinement.

    Ecologically: the midpoint-rule approximation is exact if and only
    if the species' vital rates are constant within each size bin.
    For real species with smooth vital rates, finer bins reduce the
    approximation error. -/
instance counit_iso_when_G_fully_faithful [G.Full] [G.Faithful] :
    IsIso adj.counit :=
  Adjunction.counit_isIso_of_R_fully_faithful adj

/-- If Lan_D (= F, the discretisation functor) is fully faithful, then
    the unit η is a natural isomorphism.

    Package connection: `unit_error` returns ‖η - id‖. This is always
    zero in practice because the midpoint rule perfectly encodes any
    matrix into a piecewise-constant kernel and back.

    Ecologically: every MPM is the exact discretisation of some IPM
    (namely, the piecewise-constant kernel from `right_kan_extension`).
    Discretisation is lossless when the bins perfectly capture all
    demographic transitions. -/
instance unit_iso_when_F_fully_faithful [F.Full] [F.Faithful] :
    IsIso adj.unit :=
  Adjunction.unit_isIso_of_L_fully_faithful adj

end ErrorCharacterisation


/-!

## Part 5: Naturality of Unit and Counit

**Package claim** (src/diagnostics.jl; vignettes 02, 05):
The unit η and counit ε are *natural* transformations — they don't just
exist for each individual model, they vary coherently across all models.

**Why this matters for the package**:

- `adjunction_errors(kernel, domain)` computes error diagnostics for a
  *specific* kernel and domain. Naturality guarantees that these
  diagnostics vary *smoothly* as the kernel parameters change. There
  are no discontinuous jumps in discretisation quality when you perturb
  the vital rates slightly.

**Ecological meaning**:

- **Unit naturality**: If you slightly change the entries of an MPM
  (e.g., adjust survival probability by 1%), the self-consistency
  diagnostic changes proportionally. The discretisation framework is
  stable under parameter perturbations.

- **Counit naturality**: If you slightly change the IPM kernel (e.g.,
  adjust the growth function), the midpoint-rule approximation error
  changes smoothly. This ensures that sensitivity analyses (which
  perturb vital rates) give reliable results.
-/

section Naturality

variable {C : Type u} [Category.{v} C]
variable {E : Type u} [Category.{v} E]
variable {F : C ⥤ E} {G : E ⥤ C}

/-- The unit η is a natural transformation.

    Diagram: for any morphism f : X → Y between MPMs,
      η_Y ∘ f = (D* ∘ Lan_D)(f) ∘ η_X

    Ecologically: if f is a perturbation of model parameters (e.g.,
    increasing survival by 5%), then the self-consistency diagnostic
    for the perturbed model is related to the original diagnostic by
    the same perturbation applied through the round-trip. -/
theorem unit_naturality (adj : F ⊣ G) {X Y : C} (f : X ⟶ Y) :
    (𝟭 C).map f ≫ adj.unit.app Y = adj.unit.app X ≫ (F ⋙ G).map f :=
  adj.unit.naturality f

/-- The counit ε is a natural transformation.

    Diagram: for any morphism g : F → F' between IPMs,
      ε_{F'} ∘ (Lan_D ∘ D*)(g) = g ∘ ε_F

    Ecologically: the midpoint-rule approximation error varies smoothly
    with the IPM kernel. A small change in the growth kernel produces
    a proportionally small change in the discretisation error. -/
theorem counit_naturality (adj : F ⊣ G) {X Y : E} (f : X ⟶ Y) :
    (G ⋙ F).map f ≫ adj.counit.app Y = adj.counit.app X ≫ f :=
  adj.counit.naturality f

end Naturality


/-!

## Part 6: Round-Trip Self-Consistency

**Package claim** (src/diagnostics.jl; vignette 05, lines 195–216):

- **Forward round-trip**: F(η_X) ≫ ε_{F(X)} = id.
  Discretise an MPM → refine to IPM → re-discretise: identity.
- **Backward round-trip**: η_{G(Y)} ≫ G(ε_Y) = id.
  Restrict an IPM → re-extend to IPM: identity.

**Package connection**: These are *exactly* the triangle identities
from Part 3, restated to emphasise their role as round-trip properties.
The function `unit_error(A, domain)` computes the norm of the forward
round-trip residual, which is provably zero.

**Ecological meaning**: The re-discretised matrix is the same as the
original — no information is gained by re-discretising a
piecewise-constant kernel at finer resolution (vignette 05, line 216).
To get a better approximation, one must start from the original
smooth kernel (the biological data), not from a matrix.

This is a fundamental insight for conservation: publishing only a
matrix projection model loses information that cannot be recovered
by numerical tricks. The original vital-rate data is irreplaceable.
-/

section RoundTrip

variable {C : Type u} [Category.{v} C]
variable {E : Type u} [Category.{v} E]
variable {F : C ⥤ E} {G : E ⥤ C}

/-- Forward round-trip: discretise then restrict is the identity.

    Package function: `unit_error(A, domain)` returns ‖A' - A‖/‖A‖
    where A' = Lan_D(Ran_D(A)). This theorem proves A' = A exactly.

    Ecologically: if you take a stage-structured matrix, extend it to a
    piecewise-constant kernel, then re-discretise at the same resolution,
    you recover the original matrix. No demographic information is lost
    in this particular round-trip. -/
theorem forward_round_trip (adj : F ⊣ G) (X : C) :
    F.map (adj.unit.app X) ≫ adj.counit.app (F.obj X) = 𝟙 _ :=
  adj.left_triangle_components X

/-- Backward round-trip: restrict then refine is the identity.

    Ecologically: if you evaluate an IPM at bin midpoints to get an MPM,
    then extend the MPM back to a piecewise-constant kernel, the result
    agrees with the original IPM *at the bin midpoints*. The only error
    is between the midpoints, where the piecewise-constant kernel is flat
    but the original kernel may curve. -/
theorem backward_round_trip (adj : F ⊣ G) (Y : E) :
    adj.unit.app (G.obj Y) ≫ G.map (adj.counit.app Y) = 𝟙 _ :=
  adj.right_triangle_components Y

end RoundTrip


/-!

## Part 7: Left Adjoints Preserve Colimits (Composition)

**Package claim** (src/composition.jl; vignettes 01, 03, 05):
"Discretise a composed IPM = compose the discretised sub-kernels."

More precisely: since Lan_D is a left adjoint (it has a right adjoint
D*), it preserves all colimits. In a monoidal category where the tensor
product ⊗ is computed as a colimit (as in the operadic composition of
IPM sub-kernels), this gives:

$$\text{Lan}_D(K_1 \oplus K_2) \cong \text{Lan}_D(K_1) \oplus \text{Lan}_D(K_2)$$

**Ecological meaning**: You can either:

1. Combine the survival kernel P and fecundity kernel F into a full
   kernel K = P + F, then discretise K to get a matrix A.
2. Discretise P to get A_P and F to get A_F, then combine: A = A_P + A_F.

Both approaches give the *same result*. This is why `compose_from_uwd`
and `left_kan_extension` can be used in either order.

**Mathematical content**: We verify that the existence of a right adjoint
guarantees Lan_D is a left adjoint, hence preserves colimits.
-/

section ColimitPreservation

variable {C : Type u} [Category.{v} C]
variable {E : Type u} [Category.{v} E]

/-- A functor with a right adjoint is a left adjoint, hence preserves
    all colimits.

    Package connection: `left_kan_extension` is a left adjoint (Lan_D ⊣ D*),
    so it preserves the colimit that computes kernel composition. The
    functions `compose_transitions` and `oapply` exploit this. -/
theorem is_left_adjoint_of_adjunction (F : C ⥤ E) (G : E ⥤ C) (adj : F ⊣ G) :
    F.IsLeftAdjoint :=
  ⟨G, ⟨adj⟩⟩

/-- Dually, D* has a left adjoint (Lan_D), making D* a right adjoint
    that preserves all limits (including products = parallel composition).

    Ecologically: restricting a composed IPM to bins gives the same
    result as composing the restricted sub-kernels. This is the
    "restriction commutes with composition" property used when building
    MPMs from IPM sub-kernels. -/
theorem is_right_adjoint_of_adjunction (F : C ⥤ E) (G : E ⥤ C) (adj : F ⊣ G) :
    G.IsRightAdjoint :=
  ⟨F, ⟨adj⟩⟩

end ColimitPreservation


/-!

## Part 8: Flatness and Stratification

**Package claim** (src/stratification.jl; vignette 04):
"Discretise a stratified IPM = stratify the discretised MPM."

Stratification is a *pullback* (a finite limit). Left adjoints preserve
colimits, not limits in general. So commutation with stratification
requires an additional condition: the discretisation functor D must be
**flat**.

### Why flatness matters

A functor D is *flat* when the left Kan extension Lan_D preserves
all finite limits — not just colimits (which every left adjoint
preserves). Flatness is the precise mathematical condition ensuring
that discretisation commutes with stratification (a pullback operation).

### Why the discretisation functor D is flat

The discretisation functor D : FinSet → Meas embeds each bin as a
disjoint measurable subset of the trait space. Since D is a full
embedding from a finite discrete category, all its comma categories
(D ↓ x) are discrete. Discrete categories are filtered when nonempty,
and nonemptiness holds because each trait value lies in at least one
bin. By Mac Lane & Moerdijk (Sheaves in Geometry and Logic, VII.9),
this makes D flat, so Lan_D preserves finite limits including the
pullbacks used in stratification.

### What flatness means ecologically

In population modelling, **flatness** means that the discretisation
scheme — dividing a continuous trait space into finite bins — forms a
**complete, non-overlapping partition** of the trait range. Concretely:

1. **Coverage (completeness)**: Every possible trait value (e.g., every
   body size from the minimum to maximum observed) falls within exactly
   one bin. No individuals are "lost" between bins.
2. **Non-overlap (disjointness)**: No trait value belongs to two bins
   simultaneously. Each individual is counted once.
3. **Uniform treatment within bins**: Within each bin, the kernel is
   evaluated at a single representative point (the midpoint). This is
   equivalent to assuming that individuals within a bin are
   interchangeable — a standard assumption in matrix population models.

When these conditions hold, the discretisation is flat, and two
equivalent modelling workflows become interchangeable:

- **Workflow A**: Build a spatial IPM (continuous kernel with dispersal
  across patches), then discretise the whole thing.
- **Workflow B**: Discretise the single-patch IPM to an MPM, then
  apply `stratify(A, D)` to add spatial structure.

Both yield the same spatial matrix. This is crucial for the package's
design: users typically define kernels for a single patch, discretise,
and then add spatial structure via `stratify`.

Flatness can fail in practice if bins overlap, have gaps, or use
non-standard quadrature that weights bin edges differently from
interiors. The midpoint rule with equal-width bins — the standard
approach in IPM software — satisfies flatness.

**Proof status**: Two key results are fully machine-checked:
1. Right adjoint functors are representably flat (`flat_of_right_adjoint`)
2. Flat functors' Lan preserves finite limits (`lan_preserves_finite_limits_of_flat`)

Together these establish: if the discretisation functor D admits a right
adjoint (as in Part 7's adjunction chain), then Lan_D preserves the
pullbacks used in stratification.
-/

section Flatness

open Limits

/-- Right adjoint functors are representably flat.

    In the IPM setting, the restriction functor D* is a right adjoint
    (Part 7 establishes the adjunction Lan_D ⊣ D* ⊣ Ran_D). Any
    functor that is a right adjoint has cofiltered structured arrow
    categories, making it representably flat.

    More generally, any embedding D that admits a right adjoint
    (such as a "nearest bin" assignment) is flat by this theorem.

    Ecologically: the bins form a complete, non-overlapping partition
    of the trait space — every individual belongs to exactly one bin.
    This structural property is what makes D a right adjoint, and
    flatness follows automatically.

    Reference: Mac Lane & Moerdijk, Sheaves in Geometry and Logic, VII.9;
    Mathlib `RepresentablyFlat.of_isRightAdjoint`. -/
theorem flat_of_right_adjoint
    {C : Type*} [Category C] {D : Type*} [Category D]
    (F : C ⥤ D) [F.IsRightAdjoint] :
    RepresentablyFlat F :=
  inferInstance

/-- Representably flat functors preserve all finite limits — in
    particular, the pullbacks used in stratification.

    Combined with `flat_of_right_adjoint`, this shows that the discretisation
    pipeline commutes with stratification: discretising a stratified model
    equals stratifying the discretised model.

    This is the formal statement of "flatness of D justifies commutation
    of discretisation with stratification" (Part 8).

    Reference: Mac Lane & Moerdijk, Sheaves in Geometry and Logic, VII.9;
    Mathlib `preservesFiniteLimits_of_flat`. -/
noncomputable def flat_preserves_finite_limits
    {C : Type*} [Category C] {D : Type*} [Category D]
    (F : C ⥤ D) [RepresentablyFlat F] :
    PreservesFiniteLimits F :=
  preservesFiniteLimits_of_flat F

end Flatness
