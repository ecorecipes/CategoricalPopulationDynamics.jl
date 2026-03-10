import CpmProofs.StochCat
import Mathlib.Probability.Kernel.Integral
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-!

*Source: `Integration.lean`*

## Part 2: Integration Along Kernels

Given a kernel `κ : X ⟶ Y` and an observable `f : Y → ℝ`, we can
integrate `f` against the kernel at each point `x : X` to obtain a new
observable on `X`. This is the **integration-along** operation:

$$(\text{integrateAlong}\ κ\ f)(x) = \int_Y f(y)\, \mathrm{d}κ_x(y)$$

This operation is fundamental to the Kan extension story:

- For **deterministic** kernels, integration reduces to function
  composition: `integrateAlong (det f) g = g ∘ f`.
- For **composite** kernels, integration satisfies a **Fubini-type**
  factorization: integrating along `κ ≫ η` equals first integrating
  along `η`, then along `κ`.

These two facts are the workhorses of the bridge theorem (Part 4).
-/

open CategoryTheory
open ProbabilityTheory
open MeasureTheory

universe u

namespace CpmProofs

/-- Integrate a real-valued observable against a kernel.

Given `κ : X ⟶ Y` and `f : Y → ℝ`, produces `X → ℝ` by
`x ↦ ∫ f dκ_x`. This is the "expected value" operation that turns
a random transition into a deterministic function on observables.

In Fritz's notation, this corresponds to the integration map
`E_κ : (Y → ℝ) → (X → ℝ)` induced by the Markov kernel κ. -/
noncomputable def integrateAlong {X Y : MeasObj} (κ : X ⟶ Y) (f : Y → ℝ) : X → ℝ :=
  fun x => ∫ y, f y ∂(κ x)

/-- **Integration along a deterministic kernel recovers composition.**

If `f : X → Y` is a measurable function and `g : Y → ℝ` is an
observable, then integrating `g` against the Dirac kernel `det f` simply
evaluates `g ∘ f`:

$$\int g\, \mathrm{d}\delta_{f(x)} = g(f(x))$$

This is the fundamental property connecting the deterministic world
(**Meas**) to the stochastic world (**Stoch**): deterministic kernels
act on observables by precomposition. -/
theorem integrateAlong_det
    {X Y : MeasObj} [MeasurableSingletonClass Y]
    (f : X → Y) (hf : Measurable f) (g : Y → ℝ) :
    integrateAlong (MeasObj.det f hf) g = g ∘ f := by
  ext x
  simp only [integrateAlong, Function.comp, MeasObj.det,
    Kernel.integral_deterministic hf]

/-- **Integration along a composite kernel = iterated integration.**

For kernels `κ : X ⟶ Y` and `η : Y ⟶ Z` and an observable `f : Z → ℝ`:

$$\int f\, \mathrm{d}(\eta \circ_\kappa \kappa)_x
= \int_Y \left(\int_Z f(z)\, \mathrm{d}\eta_y(z)\right) \mathrm{d}\kappa_x(y)$$

This is the **Fubini property** for kernel composition. It tells us that
composing kernels and then integrating is the same as integrating in
two stages — first the inner kernel η, then the outer kernel κ.

This property is essential for the bridge theorem: it allows us to
decompose integration against a measure μ into an outer integral over
fibers (via the pushforward D_*μ) and an inner integral within each
fiber (via the conditional kernel κ_y). -/
theorem integrateAlong_comp
    {X Y Z : MeasObj} (κ : X ⟶ Y) (η : Y ⟶ Z) (f : Z → ℝ)
    (hf_int : ∀ x, Integrable f ((η ∘ₖ κ) x)) :
    integrateAlong (κ ≫ η) f
      = fun x => ∫ y, integrateAlong η f y ∂(κ x) := by
  ext x
  simp only [integrateAlong]
  exact Kernel.integral_comp (hf_int x)

/-- Extensionality for integration along equal kernels. -/
theorem integrateAlong_ext
    {X Y : MeasObj} {κ η : X ⟶ Y} {f : Y → ℝ}
    (hκη : κ = η) :
    integrateAlong κ f = integrateAlong η f := by
  cases hκη
  rfl

end CpmProofs
