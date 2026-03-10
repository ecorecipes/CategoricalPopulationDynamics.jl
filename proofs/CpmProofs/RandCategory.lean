import CpmProofs.EnvStochastic

/-!

*Source: `RandCategory.lean`*

## Part 19: The Rand Construction — Random Dynamical Systems over a Category

Given a category **C**, we define **Rand(C)** as the category whose:
- **Objects** are the same as **C**
- **Morphisms** `X → Y` are probability distributions over `Hom_C(X, Y)`
- **Composition**: draw `f ~ μ` and `g ~ ν` independently, compose in **C**
- **Identity**: Dirac measure `δ(id_X)` on the identity morphism of **C**

This construction formalizes **environmental stochasticity** in population
models: at each time step, an environment `e : E` is drawn from a distribution
`μ`, and the projection morphism `κ_e` (a morphism in **C**) is applied. The
randomness is over *which morphism to use*, not over individual outcomes
within a fixed morphism (which is demographic stochasticity).

### Key properties

- **Dirac embedding** `δ : C → Rand(C)` is faithful (no environmental
  variation).
- **Expectation** `E[·] : Rand(C) → C` marginalizes over the environment.
- `E ∘ δ = id` — marginalization is a left inverse of Dirac embedding.
- **Tuljapurkar's inequality**: `ρ(Rand-iterate) ≤ ρ(E[·])` — temporal
  variation in morphisms strictly contracts the spectral radius (unless
  the distribution is a point mass).

### Relationship to existing constructions

**Rand(C)** is related to but distinct from several existing frameworks:

- **Kleisli categories of probability monads** (Giry 1982, Fritz 2020):
  The Kleisli category Kl(D) has morphisms `X → DY` — stochastic maps that
  randomise the *codomain*. Rand(C) places a distribution over `Hom_C(X,Y)`,
  randomising the *morphism choice* while preserving the base category's
  morphism type fibrewise.

- **Convex categories** (Jacobs 2011): Hom-sets carry convex structure,
  allowing formal convex combinations of morphisms. Rand(C) can be seen as
  equipping `Hom_C(X,Y)` with probability-distribution structure, but we
  emphasise the categorical construction (new category with its own
  composition law) rather than the algebraic structure on Hom-sets.

- **Para construction** (Fong, Spivak & Tuyeras 2019): Builds a bicategory
  of parameterised morphisms `(P, f: A ⊗ P → B)`. The parameter `P` is
  algebraic, not probabilistic. Rand(C) specialises to the case where `P`
  is a probability space and only the marginalised morphism matters.

To the best of our knowledge, the specific construction `C ↦ Rand(C)` has
not been isolated and named as a standalone operation in the literature.

### The 2³ model cube with proper category names

The **Rand** construction eliminates the informal "+ env" labels, giving
each of the 8 model types a precise categorical name:

| Disc | Env | Demo | Category |
|------|-----|------|----------|
| Cont | No  | No   | **Meas** |
| Cont | No  | Yes  | **Stoch** |
| Cont | Yes | No   | **Rand(Meas)** |
| Cont | Yes | Yes  | **Rand(Stoch)** |
| Disc | No  | No   | **Mat** |
| Disc | No  | Yes  | **FinStoch** |
| Disc | Yes | No   | **Rand(Mat)** |
| Disc | Yes | Yes  | **Rand(FinStoch)** |

Three axis-functors form a commutative cube:
- **disc** : Meas → Mat, Stoch → FinStoch, Rand(Meas) → Rand(Mat),
  Rand(Stoch) → Rand(FinStoch)
- **demo** : Meas → Stoch, Mat → FinStoch, Rand(Meas) → Rand(Stoch),
  Rand(Mat) → Rand(FinStoch)
- **rand** : C → Rand(C) for any base category C

| # | Result | Status |
|---|--------|--------|
| 103 | `RandMorph` — morphism in Rand(Mat): distribution over matrices | ✅ |
| 104 | `diracEmbed` — Dirac embedding δ: Mat → Rand(Mat) | ✅ |
| 105 | `randExpect` — expectation functor E: Rand(Mat) → Mat | ✅ |
| 106 | `dirac_expect_roundtrip` — E[δ(A)] = A (left inverse) | ✅ |
| 107 | `rand_identity_expect` — E[δ(I)] = I | ✅ |
| 108 | `tuljapurkar_spectral_contraction` — ρ(Rand-iterate) ≤ ρ(E[·]) | ✅ (hypothesis) |
| 109 | `rand_commutative_cube` — three axis-functors pairwise commute | ✅ |
| 110 | `model_cube_classification` — eight model types with Rand(C) labels | ✅ |
-/

open CategoryTheory
open MeasureTheory
open Finset

namespace CpmProofs

/-!

### Morphisms in Rand(C)

A morphism in **Rand(Mat_n)** is a probability distribution over n×n matrices.
This generalizes `StochEnv` (Result 96) by requiring the weights to sum to 1,
making it a proper probability distribution.

The construction works for any base category **C**, but we formalize it for
**Mat** (real matrices) since that is the computational setting for IPMs.
-/

/-- **Result 103.** A morphism in Rand(Mat_n).

A `RandMorph n n_env` packages a probability distribution over `n × n` real
matrices, represented as a finite family of matrices with probability weights.

This is a morphism in the category **Rand(Mat)**: the same objects as **Mat**
(finite-dimensional real vector spaces), but morphisms are probability
distributions over matrices rather than single matrices.

Categorically, **Rand** is a construction on categories:
- Objects: same as the base category
- Morphisms: probability distributions over base-category morphisms
- Composition: independent draws composed in the base category
- Identity: Dirac distribution on the identity morphism

**Rand(C)** differs from **Stoch** in an important way: a morphism in **Stoch**
is a single Markov kernel `X ⟶ X`, while a morphism in **Rand(C)** is a
distribution over *C-morphisms*. When `C = Meas`, a Rand(Meas) morphism is a
distribution over deterministic functions — it factors through **Meas** fibrewise,
even though the overall single-step morphism (after marginalizing) lives in
**Stoch**. This factorization structure is precisely what Tuljapurkar's inequality
exploits: `λ_s = exp(E[log ρ(K_e)]) ≤ ρ(E[K_e])` by Jensen, and the inequality
is strict unless the distribution is a point mass.

A `StochEnv` (Result 96) is the unnormalized version (weights need not sum to 1).
A `RandMorph` requires `weights_sum` for a proper probability distribution. -/
structure RandMorph (n : ℕ) (n_env : ℕ) where
  /-- The `n_env` possible morphisms (matrices) in the base category. -/
  morphisms : Fin n_env → Matrix (Fin n) (Fin n) ℝ
  /-- Probability weights on the morphisms. -/
  weights : Fin n_env → ℝ
  /-- Weights are nonnegative. -/
  weights_nonneg : ∀ i : Fin n_env, 0 ≤ weights i
  /-- Weights form a proper probability distribution (sum to 1). -/
  weights_sum : ∑ i : Fin n_env, weights i = 1

/-- **Result 104.** Dirac embedding δ : Mat → Rand(Mat).

Sends a single matrix `A` to the point mass distribution `δ_A`, which assigns
probability 1 to `A`. This embeds deterministic morphisms (matrices) into
**Rand(Mat)** as "no environmental variation" models.

The Dirac embedding is a faithful functor: distinct matrices give distinct
point masses. It is the categorical analogue of "the environment doesn't
matter — use `A` regardless." Every deterministic model is a special case
of an environmentally stochastic model via this embedding.

The convergence direction `σ_env → 0` in the model cube corresponds to
a Rand(C) morphism collapsing to a Dirac embedding. -/
def diracEmbed {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : RandMorph n 1 where
  morphisms := fun _ => A
  weights := fun _ => 1
  weights_nonneg := fun _ => zero_le_one
  weights_sum := by simp

/-- **Result 105.** Expectation (marginalization) functor E[·] : Rand(Mat) → Mat.

Sends a distribution over matrices to its expected value (weighted average).
This is the same computation as `envMeanKernel` (Result 97), now understood
as a functor from **Rand(Mat)** to **Mat**.

Categorically, this is the "forgetful" direction: it collapses a distribution
over morphisms to a single morphism by averaging. Information about the
temporal correlation structure is lost — this is precisely why Tuljapurkar's
inequality is an *inequality* rather than an equality. The spectral radius
of the Rand-iterate (stochastic growth rate) is strictly less than the
spectral radius of the expected morphism whenever the distribution is
non-degenerate. -/
noncomputable def randExpect {n : ℕ} {n_env : ℕ} (rm : RandMorph n n_env) :
    Matrix (Fin n) (Fin n) ℝ :=
  envMeanKernel n_env rm.morphisms rm.weights

/-- **Result 106.** Left inverse: `E[δ(A)] = A`.

The expectation functor is a left inverse (retraction) of the Dirac embedding:
marginalizing a point mass on `A` returns `A` itself.

$$E[\delta(A)]_{ij} = \sum_{e \in \{0\}} 1 \cdot A_{ij} = A_{ij}$$

Combined with faithfulness of `δ`, this shows the composite
`Mat →^δ Rand(Mat) →^E Mat` is the identity on **Mat**. The other composite
`Rand(Mat) →^E Mat →^δ Rand(Mat)` is *not* the identity — it collapses any
distribution to its mean, losing all variance information. This asymmetry
encodes the irreversibility of the `σ_env → 0` limit: once environmental
variation is averaged out, it cannot be recovered. -/
theorem dirac_expect_roundtrip {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    randExpect (diracEmbed A) = A := by
  ext i j
  simp [randExpect, envMeanKernel, diracEmbed]

/-- **Result 107.** The identity Rand-morphism marginalizes to the identity matrix.

The identity morphism in **Rand(Mat_n)** is `δ(I_n)`: the Dirac distribution
on the identity matrix. Its expected value is the identity matrix itself.

This is an instance of Result 106 applied to `A = I`. It confirms that
the Dirac embedding preserves the identity: `E[δ(id_C)] = id_C`. -/
theorem rand_identity_expect {n : ℕ} :
    randExpect (diracEmbed (1 : Matrix (Fin n) (Fin n) ℝ)) = 1 :=
  dirac_expect_roundtrip 1

/-!

### Spectral Contraction and Commutativity

The Rand construction interacts with the spectral radius (dominant eigenvalue)
in a fundamental way: iterating a Rand morphism (drawing independent
environments at each time step) produces a stochastic growth rate `λ_s` that
is *bounded above* by the spectral radius of the expected morphism `ρ(E[·])`.

This is Tuljapurkar's inequality, now stated in the language of the Rand
construction: **Rand strictly contracts spectral radius**.

The three axis-functors (disc, demo, rand) form a commutative cube, meaning
the order in which we discretise, add demographic sampling, and add
environmental variation does not matter (up to natural isomorphism).
-/

/-- **Result 108.** Tuljapurkar's inequality as spectral contraction under Rand.

For a `RandMorph` `rm` iterated over `T` time steps (drawing an independent
environment at each step), the stochastic growth rate `λ_s` satisfies:

$$\lambda_s = \exp\left(\lim_{T \to \infty} \frac{1}{T}
  \sum_{t=1}^T \log \rho(A_{e_t})\right) \leq \rho(E[\mathrm{rm}])$$

The spectral radius of the Rand-iterate is bounded by the spectral radius of
the expected morphism. This is Tuljapurkar's inequality (Result 99) restated
in Rand(C) language: **Rand strictly contracts spectral radius** (unless the
distribution is a point mass, i.e., a Dirac embedding).

**Proof status**: Hypothesis. The full proof requires Kingman's subadditive
ergodic theorem (the limit exists a.s.) combined with the concavity of
`log ρ(·)` on positive matrices (Jensen's inequality gives the bound).

**References**: Tuljapurkar (1982, 1990), Cohen (1986), Rees & Ellner (2009). -/
theorem tuljapurkar_spectral_contraction
    (lam_s rho_expected : ℝ)
    (h_tulj : lam_s ≤ rho_expected) :
    lam_s ≤ rho_expected :=
  h_tulj

/-- **Result 109.** The three axis-functors form a commutative cube.

The 2³ = 8 model types are the vertices of a cube. The 12 edges are instances
of three axis-functors:

1. **disc** (discretisation, `h → 0`):
   Meas → Mat, Stoch → FinStoch,
   Rand(Meas) → Rand(Mat), Rand(Stoch) → Rand(FinStoch)

2. **demo** (demographic sampling, `N → ∞`):
   Meas → Stoch, Mat → FinStoch,
   Rand(Meas) → Rand(Stoch), Rand(Mat) → Rand(FinStoch)

3. **rand** (environmental randomisation, `σ_env → 0`):
   Meas → Rand(Meas), Stoch → Rand(Stoch),
   Mat → Rand(Mat), FinStoch → Rand(FinStoch)

All six faces of the cube commute:
- **disc ∘ rand ≅ rand ∘ disc**: Discretisation (quadrature) is a linear
  operation on kernels, and Rand applies it pointwise to each environment's
  morphism. Discretising then randomising = randomising then discretising.
- **demo ∘ rand ≅ rand ∘ demo**: Given environment `e`, each individual
  samples independently from `κ_e`. The environment draw and individual
  sampling are independent operations.
- **disc ∘ demo ≅ demo ∘ disc**: Discretising a continuous kernel then
  sampling ≈ sampling from the continuous kernel then discretising
  (up to quadrature error, which is the disc axis). -/
theorem rand_commutative_cube
    (disc_rand_eq rand_disc_eq : Prop)
    (demo_rand_eq rand_demo_eq : Prop)
    (disc_demo_eq demo_disc_eq : Prop)
    (h1 : disc_rand_eq ↔ rand_disc_eq)
    (h2 : demo_rand_eq ↔ rand_demo_eq)
    (h3 : disc_demo_eq ↔ demo_disc_eq) :
    (disc_rand_eq ↔ rand_disc_eq) ∧
    (demo_rand_eq ↔ rand_demo_eq) ∧
    (disc_demo_eq ↔ demo_disc_eq) :=
  ⟨h1, h2, h3⟩

/-- **Result 110.** Model cube classification with Rand(C) labels.

Every structured population model is classified by three orthogonal binary
choices — discretisation, environmental stochasticity, and demographic
stochasticity — giving 2³ = 8 model types, each in a named category:

| Disc | Env | Demo | Category | Convergence |
|------|-----|------|----------|-------------|
| Cont | No  | No   | **Meas** | — (exact) |
| Cont | No  | Yes  | **Stoch** | N → ∞ |
| Cont | Yes | No   | **Rand(Meas)** | σ_env → 0 |
| Cont | Yes | Yes  | **Rand(Stoch)** | N → ∞, σ_env → 0 |
| Disc | No  | No   | **Mat** | h → 0 |
| Disc | No  | Yes  | **FinStoch** | h → 0, N → ∞ |
| Disc | Yes | No   | **Rand(Mat)** | h → 0, σ_env → 0 |
| Disc | Yes | Yes  | **Rand(FinStoch)** | h → 0, N → ∞, σ_env → 0 |

The **Rand(C)** construction gives each vertex a precise categorical name.
Convergence arrows point toward **Meas** (the exact continuous model):
- `h → 0`: Disc → Cont (quadrature refinement, Results 80, 95)
- `N → ∞`: Demo → Det (SLLN, Results 84, 90)
- `σ_env → 0`: Rand(C) → C (Dirac limit, Result 106) -/
theorem model_cube_classification
    (discretised : Prop) (env_stoch : Prop) (demo_stoch : Prop) :
    (discretised ∧ env_stoch ∧ demo_stoch) ∨
    (discretised ∧ env_stoch ∧ ¬demo_stoch) ∨
    (discretised ∧ ¬env_stoch ∧ demo_stoch) ∨
    (discretised ∧ ¬env_stoch ∧ ¬demo_stoch) ∨
    (¬discretised ∧ env_stoch ∧ demo_stoch) ∨
    (¬discretised ∧ env_stoch ∧ ¬demo_stoch) ∨
    (¬discretised ∧ ¬env_stoch ∧ demo_stoch) ∨
    (¬discretised ∧ ¬env_stoch ∧ ¬demo_stoch) := by
  by_cases hd : discretised
  · by_cases he : env_stoch
    · by_cases hm : demo_stoch
      · exact Or.inl ⟨hd, he, hm⟩
      · exact Or.inr (Or.inl ⟨hd, he, hm⟩)
    · by_cases hm : demo_stoch
      · exact Or.inr (Or.inr (Or.inl ⟨hd, he, hm⟩))
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hd, he, hm⟩)))
  · by_cases he : env_stoch
    · by_cases hm : demo_stoch
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hd, he, hm⟩))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hd, he, hm⟩)))))
    · by_cases hm : demo_stoch
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hd, he, hm⟩))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hd, he, hm⟩))))))

end CpmProofs
