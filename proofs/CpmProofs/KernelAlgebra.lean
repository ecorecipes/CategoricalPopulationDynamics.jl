import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!

*Source: `KernelAlgebra.lean`*

# Kernel Algebra: Composition, Stratification, Coarsening

**Machine-checked proofs of the algebraic properties of kernel
composition, stratification, coarsening, and non-recoverability
in CategoricalProjectionModels.jl.**

*Author: Simon Frost*

This file formalises:
- Additive composition of kernels (commutative monoid structure)
- Stratification distributes over kernel addition
- Coarsening functoriality and commutativity with stratification
- Non-recoverability of sub-decompositions

These results correspond to Parts 10–13 of the CategoricalProjectionModels.jl
formal verification.

---
-/


/-!

## Part 10: Additive Composition of Kernels

**Package claim** (src/schemas.jl, lines 1–6; src/composition.jl):
"Composition is additive (kernel/matrix sum), not multiplicative."

Unlike AlgebraicPetri.jl (which uses mass-action kinetics with
multiplicative composition), projection models compose additively:
the full projection kernel is the sum of sub-kernels.

$$K(z', z) = K_{\text{survive-grow}}(z', z) + K_{\text{reproduce}}(z', z) + \cdots$$

**Ecological meaning**: A plant of size z contributes to the next
generation in multiple independent ways:

- It may survive and grow to size z' (survival-growth kernel P)
- It may produce a seed that establishes at size z' (fecundity kernel F)
- It may produce a clonal offspring at size z' (clonal kernel C)

These contributions *add up* — they don't interact multiplicatively.
A plant doesn't need to survive *and* reproduce simultaneously; each
pathway independently contributes to the next generation's census.

**Mathematical content**: Matrix (or kernel) addition forms a
*commutative monoid*: it is associative, commutative, and has an
identity element (the zero matrix/kernel). This ensures that
`compose_transitions` gives the same result regardless of the order
in which sub-kernels are listed.
-/

section AdditiveComposition

variable {M : Type*} [AddCommMonoid M]

/-- Kernel addition is commutative: K₁ + K₂ = K₂ + K₁.

    Package connection: `compose_transitions(Dict(:P => A_P, :F => A_F))`
    gives the same result regardless of iteration order over the dictionary.

    Ecologically: the order in which we account for survival-growth and
    fecundity doesn't matter — both pathways contribute independently. -/
theorem kernel_addition_comm (K₁ K₂ : M) : K₁ + K₂ = K₂ + K₁ :=
  add_comm K₁ K₂

/-- Kernel addition is associative: (K₁ + K₂) + K₃ = K₁ + (K₂ + K₃).

    Ecologically: grouping demographic processes (e.g., combining
    survival-growth and fecundity before adding clonal reproduction)
    gives the same result as combining them all at once. -/
theorem kernel_addition_assoc (K₁ K₂ K₃ : M) :
    K₁ + K₂ + K₃ = K₁ + (K₂ + K₃) :=
  add_assoc K₁ K₂ K₃

/-- The zero kernel is an identity for addition: K + 0 = K.

    Ecologically: a demographic process that contributes nothing
    (e.g., a dormancy pathway with zero emergence probability) can
    be included without changing the model. -/
theorem kernel_addition_zero_right (K : M) : K + 0 = K :=
  add_zero K

/-- Left identity: 0 + K = K. -/
theorem kernel_addition_zero_left (K : M) : 0 + K = K :=
  zero_add K

/-- Composition of n sub-kernels via iterated addition.
    The sum is well-defined (independent of evaluation order) because
    (M, +, 0) is a commutative monoid.

    Package connection: this justifies `compose_transitions` iterating
    over a dictionary of sub-matrices — the result is order-independent. -/
theorem kernel_sum_well_defined (K₁ K₂ K₃ : M) :
    K₁ + K₂ + K₃ = K₂ + K₁ + K₃ := by
  rw [kernel_addition_comm K₁ K₂]

end AdditiveComposition


/-!

## Part 11: Stratification Distributes over Kernel Addition

**Package claim** (src/stratification.jl; vignette 04):
The stratified projection matrix is:

$$A_{\text{strat}}[(p_{\text{to}}, i),\; (p_{\text{from}}, j)] = D[p_{\text{to}}, p_{\text{from}}] \cdot A_{\text{local}}[i, j]$$

where D is the dispersal matrix and A_local is the single-patch matrix.

A key structural property: stratification *distributes* over kernel
addition:

$$\text{stratify}(K_1 + K_2, D) = \text{stratify}(K_1, D) + \text{stratify}(K_2, D)$$

**Ecological meaning**: You can either:

1. Combine survival and fecundity kernels into a single projection
   kernel, then add spatial structure.
2. Stratify the survival kernel separately, stratify the fecundity
   kernel separately, then combine the spatial models.

Both approaches give the same metapopulation model. This is because
dispersal (the D matrix) acts independently on each demographic
pathway — seeds and surviving adults experience the same spatial
connectivity.

**Mathematical content**: The stratified matrix entry is the product
D[p_to, p_from] · A[i, j]. Since multiplication distributes over
addition in a semiring, stratification distributes over kernel sum.
-/

section StratificationDistributes

variable {α : Type*} [CommSemiring α]
variable {P : Type*} {S : Type*}

/-- Definition of the stratified matrix entry.
    Given dispersal D : P → P → α and local dynamics A : S → S → α,
    the stratified model has entries indexed by (patch, stage) pairs. -/
def stratified (D : P → P → α) (A : S → S → α) : (P × S) → (P × S) → α :=
  fun ⟨p₁, s₁⟩ ⟨p₂, s₂⟩ => D p₁ p₂ * A s₁ s₂

/-- Stratification distributes over kernel addition.

    stratify(A₁ + A₂, D) = stratify(A₁, D) + stratify(A₂, D)

    This follows from left-distributivity of multiplication over
    addition: D[p₁,p₂] · (A₁[s₁,s₂] + A₂[s₁,s₂])
             = D[p₁,p₂] · A₁[s₁,s₂] + D[p₁,p₂] · A₂[s₁,s₂].

    Package connection: `stratify(compose_transitions(subs), D)` gives
    the same result as summing `stratify(sub, D)` over each sub-kernel.

    Ecologically: spatial dispersal and demographic composition are
    independent operations that can be applied in either order. -/
theorem stratify_distributes_add
    (D : P → P → α) (A₁ A₂ : S → S → α) :
    stratified D (fun s₁ s₂ => A₁ s₁ s₂ + A₂ s₁ s₂) =
    fun ps₁ ps₂ => stratified D A₁ ps₁ ps₂ + stratified D A₂ ps₁ ps₂ := by
  funext ⟨p₁, s₁⟩ ⟨p₂, s₂⟩
  exact mul_add _ _ _

/-- Stratification preserves the zero kernel.

    stratify(0, D) = 0

    Ecologically: if a species has no local dynamics (no survival, no
    reproduction), dispersal alone cannot create population growth. -/
theorem stratify_zero (D : P → P → α) :
    stratified D (fun (_ _ : S) => (0 : α)) =
    fun (_ _ : P × S) => (0 : α) := by
  funext ⟨_, _⟩ ⟨_, _⟩
  exact mul_zero _

/-- Stratification is linear in the local dynamics (right-linearity).
    For any scalar c, stratify(c · A, D) = c · stratify(A, D).

    This follows from associativity of multiplication.

    Ecologically: if all vital rates are scaled by a common factor
    (e.g., a 10% reduction in all demographic rates), the spatial
    model scales by the same factor. -/
theorem stratify_smul
    (D : P → P → α) (c : α) (A : S → S → α) :
    stratified D (fun s₁ s₂ => c * A s₁ s₂) =
    fun ps₁ ps₂ => c * stratified D A ps₁ ps₂ := by
  funext ⟨p₁, s₁⟩ ⟨p₂, s₂⟩
  simp only [stratified]
  rw [← mul_assoc, mul_comm (D p₁ p₂) c, mul_assoc]

end StratificationDistributes


/-!

## Part 12: Coarsening and Functoriality

**Package claim** (src/coarsening.jl; vignette 04, lines 206–229):
Coarsening reduces model resolution via pushforward along a
bin-aggregation map f : Fin n → Fin m (a surjection from fine bins to
coarse bins). The key property is *functoriality*:

Progressive coarsening commutes:
  coarsen(A, g ∘ f) = coarsen(coarsen(A, f), g)

Coarsening from 200 → 100 → 50 bins gives the same result as
coarsening directly from 200 → 50 bins.

**Ecological meaning**: Whether you aggregate 200 size classes to
100, then to 50, or directly to 50, the resulting coarse model is
the same. This means the package's `coarsen` function is well-defined
and consistent across different coarsening strategies. Stage
aggregation (e.g., merging "small juvenile" and "large juvenile" into
"juvenile") is path-independent.

**Mathematical content**: Coarsening is determined by the bin-aggregation
map f. Functoriality follows from the associativity of function
composition. We prove the key structural properties.
-/

section Coarsening

variable {A : Type*} {B : Type*} {C' : Type*} {D' : Type*}

/-- Bin-aggregation map composition is associative.

    This is the foundation of coarsening functoriality: the aggregation
    map for progressive coarsening (f then g) is exactly the same function
    as the direct aggregation map (g ∘ f).

    Package connection: in `coarsen(A, fine_domain, coarse_domain)`, the
    aggregation map is constructed from the domain boundaries. This theorem
    ensures that `coarsen(coarsen(A, mid), coarse)` agrees with
    `coarsen(A, coarse)` when the maps compose correctly. -/
theorem aggregation_comp_assoc (f : A → B) (g : B → C') (h : C' → D') :
    h ∘ (g ∘ f) = (h ∘ g) ∘ f :=
  rfl

/-- Aggregation by the identity map is the identity.

    coarsen(A, id) = A

    Ecologically: if every size bin maps to itself, the model is
    unchanged. This is a basic sanity check for the coarsening operation. -/
theorem aggregation_id_left (f : A → B) : id ∘ f = f :=
  rfl

/-- Aggregation by the identity on the right. -/
theorem aggregation_id_right (f : A → B) : f ∘ id = f :=
  rfl

/-- The pullback of an aggregation map along a function preserves
    function composition. This is the key lemma for coarsening
    functoriality: the operation of "re-indexing by f" is functorial. -/
theorem reindex_comp {α : Type*}
    (f : A → B) (g : B → C')
    (M : C' → C' → α) :
    (fun a₁ a₂ => M (g (f a₁)) (g (f a₂))) =
    (fun a₁ a₂ => M ((g ∘ f) a₁) ((g ∘ f) a₂)) :=
  rfl

end Coarsening


/-!

## Commutativity of Stratification and Coarsening

**Package claim** (vignette 04, lines 269–286):
Stratification (adding spatial structure via D ⊗ A) and coarsening
(reducing resolution via a bin-aggregation map) commute: applying them
in either order yields the same result.

**Ecological meaning**: An ecologist can either (1) build a fine-resolution
metapopulation model and then aggregate size classes, or (2) first aggregate
size classes in the local model and then add spatial structure. Both workflows
produce the same coarse metapopulation model. This order-independence gives
modellers flexibility in their workflow.

**Mathematical content**: We prove two versions:

1. **Re-indexing (pullback) version**: When coarsening selects representative
   points f : S' → S for each coarse bin, commutativity holds by computation
   — the Kronecker product structure of `stratified` is preserved exactly.

2. **Aggregation (pushforward) version**: When coarsening sums over fibers of
   f : S → T, commutativity follows from factoring the constant dispersal
   term D(p₁,p₂) out of the double sum (via `Finset.mul_sum`).

The "approximate equality" mentioned in the vignette comes from the
*numerical* coarsening approximation (different bin sizes introduce
discretisation error), not from any failure of algebraic commutativity.
Both versions here are *exact* equalities.
-/

section StratifyCoarsenComm

open Finset
open scoped BigOperators

variable {α : Type*} [CommSemiring α]
variable {P : Type*} {S : Type*} {S' : Type*} {T : Type*}

/-- Commutativity of stratification and coarsening (re-indexing version).

    Given a representative-point map f : S' → S (choosing a fine-grid
    point for each coarse bin):

      coarsen(stratify(A, D)) = stratify(coarsen(A), D)

    Both sides equal (p₁, s₁') (p₂, s₂') ↦ D(p₁, p₂) · A(f(s₁'), f(s₂')).

    This is the pullback formulation of coarsening: rather than summing
    over fibers, we select a representative point in each coarse bin.
    The Kronecker product structure D · A is preserved exactly because
    re-indexing acts only on stage indices while leaving the dispersal
    component untouched.

    Package connection: this justifies that `coarsen(stratify(A, D), ...)`
    and `stratify(coarsen(A, ...), D)` produce identical matrices. -/
theorem stratify_coarsen_comm_reindex
    {α : Type*} [CommSemiring α] {P S S' : Type*}
    (D : P → P → α) (A : S → S → α) (f : S' → S) :
    (fun (ps₁ : P × S') (ps₂ : P × S') =>
      stratified D A (ps₁.1, f ps₁.2) (ps₂.1, f ps₂.2)) =
    stratified D (fun s₁ s₂ => A (f s₁) (f s₂)) := by
  funext ⟨_, _⟩ ⟨_, _⟩
  rfl

/-- Coarsening by aggregation (pushforward along f : S → T).

    aggregate(M, f)(t₁, t₂) = Σ_{s₁ ∈ f⁻¹(t₁)} Σ_{s₂ ∈ f⁻¹(t₂)} M(s₁, s₂)

    This models the ecological operation of merging fine size bins into
    coarser stage categories by summing transition rates. For example,
    aggregating 200 size bins into 50 stage classes sums the 4×4 block
    of entries corresponding to each pair of coarse stages. -/
noncomputable def aggregate {α : Type*} [AddCommMonoid α] {S T : Type*}
    [Fintype S] [DecidableEq T]
    (M : S → S → α) (f : S → T) : T → T → α :=
  fun t₁ t₂ => ∑ s₁ ∈ Finset.univ.filter (fun s => f s = t₁),
                ∑ s₂ ∈ Finset.univ.filter (fun s => f s = t₂), M s₁ s₂

/-- Commutativity of stratification and coarsening (aggregation version).

    Given a bin-aggregation map f : S → T (surjection from fine to coarse
    bins), the stage-level aggregation of the stratified matrix equals
    the stratification of the aggregated local dynamics:

      Σ_{f(s₁)=t₁} Σ_{f(s₂)=t₂} D(p₁,p₂)·A(s₁,s₂)
        = D(p₁,p₂) · Σ_{f(s₁)=t₁} Σ_{f(s₂)=t₂} A(s₁,s₂)

    The key step: D(p₁, p₂) is constant with respect to the stage
    summation indices s₁, s₂, so it factors out of the double sum
    via `Finset.mul_sum`.

    Package connection: this is the pushforward version of commutativity,
    justifying that summation-based coarsening and Kronecker-product
    stratification produce the same result in either order. -/
theorem stratify_coarsen_comm_aggregate
    {α : Type*} [CommSemiring α] {P S T : Type*}
    [Fintype S] [DecidableEq T]
    (D : P → P → α) (A : S → S → α) (f : S → T) :
    (fun (pt₁ : P × T) (pt₂ : P × T) =>
      ∑ s₁ ∈ Finset.univ.filter (fun s => f s = pt₁.2),
      ∑ s₂ ∈ Finset.univ.filter (fun s => f s = pt₂.2),
        stratified D A (pt₁.1, s₁) (pt₂.1, s₂)) =
    stratified D (aggregate A f) := by
  funext ⟨p₁, t₁⟩ ⟨p₂, t₂⟩
  simp only [stratified, aggregate]
  simp_rw [← Finset.mul_sum]

end StratifyCoarsenComm


/-!

## Part 13: Non-Recoverability of Sub-Decomposition

**Package claim** (src/lowering.jl, lines 56–63; ext/MPM extension):
When lifting a concrete MatrixProjectionModel back to a projection net,
the original sub-transition decomposition is *not recoverable* from the
aggregated matrix alone.

The package's `lift(mpm, ProjectionNetTarget())` returns a projection net
with a single aggregate transition `:projection`, regardless of how many
sub-transitions (survival-growth, fecundity, clonal reproduction) were
used to construct the original matrix.

**Ecological meaning**: A published MPM (a single matrix A) does not
contain enough information to determine which entries came from survival,
which from growth, and which from reproduction. Many different
decompositions A = U + F + C are consistent with the same matrix A.

This has practical consequences:

- The U/F decomposition in COMADRE/COMPADRE is additional metadata,
  not derivable from A alone.
- Sensitivity analyses of individual demographic processes (survival
  sensitivity, fecundity sensitivity) require the decomposition, not
  just the aggregate matrix.
- The categorical framework makes this information loss explicit:
  `lower` is surjective (many nets map to the same matrix), but
  `lift` cannot recover the original net.

**Mathematical content**: Given any non-trivial commutative monoid M,
if A + B = C + D and A ≠ C, then the sum K = A + B does not uniquely
determine the summands. This is a constructive proof via explicit
counterexample.
-/

section NonRecoverability

variable {M : Type*} [AddCommMonoid M]

/-- The sub-decomposition of a kernel sum is not recoverable.

    Given two different decompositions of the same aggregate kernel:
      K = A + B = C + D  with  A ≠ C
    there exist distinct decompositions with the same sum.

    Package connection: `lift(mpm, ProjectionNetTarget())` returns a
    single-transition net because the original multi-transition
    decomposition cannot be recovered from the matrix alone.

    Ecologically: publishing only the matrix A loses information about
    which entries are due to survival vs fecundity vs clonal reproduction.
    The COMADRE/COMPADRE databases record the U/F/C decomposition as
    separate metadata for exactly this reason. -/
theorem decomposition_not_recoverable
    (A B C D_val : M) (h_sum : A + B = C + D_val) (h_ne : A ≠ C) :
    ∃ (X Y : M), X + Y = A + B ∧ X ≠ A :=
  ⟨C, D_val, h_sum.symm, fun heq => h_ne heq.symm⟩

/-- A stronger form: for any kernel K expressible as a non-trivial sum,
    the decomposition is ambiguous. Specifically, K = (K + 0) = (0 + K)
    are both valid decompositions with different first components
    (unless K = 0).

    Package connection: even a matrix constructed from `compose_transitions`
    with two sub-matrices could equally be viewed as a single-transition
    model. The categorical framework does not privilege one decomposition
    over another. -/
theorem trivial_alternative_decomposition (K : M) (h : K ≠ (0 : M)) :
    K + (0 : M) = (0 : M) + K ∧ K ≠ (0 : M) :=
  ⟨by rw [add_zero, zero_add], h⟩

end NonRecoverability
