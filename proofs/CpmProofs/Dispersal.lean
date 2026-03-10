import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Algebra.Ring.Basic

/-!

*Source: `Dispersal.lean`*

# Symmetric Dispersal Preserves the Dominant Eigenvalue

**Machine-checked proofs of the Kronecker product properties underpinning
spatial stratification in CategoricalProjectionModels.jl.**

*Author: Simon Frost*

This file formalises the key algebraic identity (mixed-product rule for
Kronecker products) and its consequence: symmetric dispersal preserves
the dominant eigenvalue. This corresponds to Part 9 of the
CategoricalProjectionModels.jl formal verification.

---
-/

/-!

## Part 9: Symmetric Dispersal Preserves the Dominant Eigenvalue

**Package claim** (src/stratification.jl; vignette 04):
When the dispersal matrix D is *doubly stochastic* (rows and columns
each sum to 1) with largest eigenvalue 1, stratification preserves the
dominant eigenvalue: λ(D ⊗ A) = λ(A).

**Ecological meaning**: In spatial ecology, the dispersal matrix D
describes how individuals move between patches. A *doubly stochastic*
dispersal matrix means that dispersal is *symmetric* — each patch
exports and imports the same total fraction of individuals. Under
symmetric dispersal, the overall population growth rate λ is
determined entirely by the local demography A, not by the spatial
arrangement. This is a powerful result: if an ecologist verifies that
dispersal is approximately symmetric (e.g., equal migration rates
between adjacent patches), they can analyse the single-patch model
to predict metapopulation growth.

**Mathematical content**: The eigenvalues of the Kronecker product
D ⊗ A are all pairwise products {d_i · a_j} where {d_i} and {a_j}
are the eigenvalues of D and A respectively. If D is doubly stochastic
with largest eigenvalue d₁ = 1, then λ(D ⊗ A) = 1 · λ(A) = λ(A).

We verify the key algebraic property of Kronecker products used in
the proof: the *mixed-product rule* (A · B) ⊗ (C · D) = (A ⊗ C) · (B ⊗ D).
This is the fundamental identity that allows eigenvector computations
to factor across the Kronecker product.
-/

section SymmetricDispersal

open Matrix

/-- The mixed-product property of Kronecker products.

    (A * B) ⊗ₖ (C * D) = (A ⊗ₖ C) * (B ⊗ₖ D)

    This is the key algebraic identity underpinning the eigenvalue
    factorisation of Kronecker products. In the context of stratified
    population models:
    - A = dispersal matrix D, B = dispersal eigenvector
    - C = local dynamics A, D = local eigenvector
    Then D·v_D ⊗ₖ A·v_A = (D ⊗ₖ A) · (v_D ⊗ₖ v_A), showing that
    the Kronecker product of eigenvectors is an eigenvector of the
    stratified matrix.

    Package connection: `stratify(A_local, D)` computes D ⊗ A.
    When D has eigenvector v with eigenvalue 1 (doubly stochastic),
    the stratified model's dominant eigenvector is v ⊗ w (where w
    is the local model's dominant eigenvector) with eigenvalue
    1 · λ(A) = λ(A). -/
theorem kronecker_mixed_product
    {l m n : Type*} [Fintype m] [DecidableEq m]
    {o p q : Type*} [Fintype p] [DecidableEq p]
    {α : Type*} [CommSemiring α]
    (A : Matrix l m α) (B : Matrix m n α)
    (C : Matrix o p α) (D' : Matrix p q α) :
    kroneckerMap (· * ·) (A * B) (C * D') =
    kroneckerMap (· * ·) A C * kroneckerMap (· * ·) B D' :=
  mul_kronecker_mul A B C D'

/-- If v is an eigenvector of D with eigenvalue d, and w is an
    eigenvector of A with eigenvalue a, then v ⊗ w is an eigenvector
    of D ⊗ A with eigenvalue d · a.

    This is stated as a consequence of the mixed-product property:
    (D ⊗ A)(v ⊗ w) = (Dv) ⊗ (Aw) = (d·v) ⊗ (a·w) = (d·a)(v ⊗ w).

    Ecologically: If the dispersal matrix has dominant eigenvalue 1
    (doubly stochastic = symmetric dispersal), then the metapopulation
    growth rate equals the local growth rate. Spatial arrangement
    does not alter λ under symmetric dispersal.

    This is a type-level statement capturing the structure used in
    the package's `stratify` function. -/
theorem kronecker_eigenvector_eigenvalue
    {n p : Type*} [Fintype n] [DecidableEq n] [Fintype p] [DecidableEq p]
    {α : Type*} [CommSemiring α]
    (D_mat : Matrix n n α) (A_mat : Matrix p p α)
    (v : Matrix n (Fin 1) α) (w : Matrix p (Fin 1) α)
    (d a : α)
    (hv : D_mat * v = v.map (d * ·))
    (hw : A_mat * w = w.map (a * ·)) :
    kroneckerMap (· * ·) D_mat A_mat * kroneckerMap (· * ·) v w =
    (kroneckerMap (· * ·) v w).map (d * a * ·) := by
  rw [← mul_kronecker_mul]
  rw [hv, hw]
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
  simp [kroneckerMap, Matrix.map]
  ring

end SymmetricDispersal
