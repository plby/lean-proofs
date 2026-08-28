import Wikipedia.HopfProblem.TriangleHolomorphicDifferentialsSpherePoles
import Wikipedia.HopfProblem.TriangleHolomorphicDifferentialsSphereInfinity

/-!
# Scalar vanishing for holomorphic differentials on the sphere

An actual scalar coefficient, analytic off zero and one, with double
poles controlled by analytic germs at those two points and fifth-order
reciprocal-coordinate decay, vanishes off the two exceptional points.
The proof constructs the entire pole-cleared function and applies
Liouville to its proved first-order decay. No line-bundle degree or
global descent assertion is an input.

The imported inverse-germ theorem also proves the entire inverse-square
case for the scalar coefficient of a holomorphic one-form.
-/

noncomputable section

open Filter Set
open scoped Topology

namespace Wikipedia.HopfProblem.TriangleHolomorphicDifferentialsSphere

/-- The explicitly extended function `z²(z-1)²F(z)` is zero everywhere
under the three supplied local analytic formulas. -/
theorem clearDoublePoles_eq_zero_of_germs {F H₀ H₁ Hinf : ℂ → ℂ}
    (hF : ∀ z, z ≠ 0 → z ≠ 1 → AnalyticAt ℂ F z)
    (hH₀ : AnalyticAt ℂ H₀ 0) (hH₁ : AnalyticAt ℂ H₁ 1)
    (hHinf : AnalyticAt ℂ Hinf 0)
    (h₀ : F =ᶠ[𝓝[≠] (0 : ℂ)] fun z => H₀ z / z ^ 2)
    (h₁ : F =ᶠ[𝓝[≠] (1 : ℂ)] fun z => H₁ z / (z - 1) ^ 2)
    (hinf : F =ᶠ[cocompact ℂ] fun z => z⁻¹ ^ 5 * Hinf z⁻¹) (z : ℂ) :
    clearDoublePoles F H₀ H₁ z = 0 :=
  entire_eq_zero_of_inverse_germ
    (clearDoublePoles_entire hF hH₀ hH₁ h₀ h₁)
    (clearedInfinityGerm_analyticAt hHinf) (by decide)
    (clearDoublePoles_eventuallyEq_infinity hinf) z

/-- The cubic-differential scalar vanishes at every ordinary finite
point. Its arbitrary original values at zero and one are not constrained. -/
theorem cubic_eq_zero_of_pole_germs {F H₀ H₁ Hinf : ℂ → ℂ}
    (hF : ∀ z, z ≠ 0 → z ≠ 1 → AnalyticAt ℂ F z)
    (hH₀ : AnalyticAt ℂ H₀ 0) (hH₁ : AnalyticAt ℂ H₁ 1)
    (hHinf : AnalyticAt ℂ Hinf 0)
    (h₀ : F =ᶠ[𝓝[≠] (0 : ℂ)] fun z => H₀ z / z ^ 2)
    (h₁ : F =ᶠ[𝓝[≠] (1 : ℂ)] fun z => H₁ z / (z - 1) ^ 2)
    (hinf : F =ᶠ[cocompact ℂ] fun z => z⁻¹ ^ 5 * Hinf z⁻¹)
    {z : ℂ} (hz₀ : z ≠ 0) (hz₁ : z ≠ 1) : F z = 0 := by
  have he := clearDoublePoles_eq_zero_of_germs hF hH₀ hH₁ hHinf h₀ h₁ hinf z
  rw [clearDoublePoles_eq_of_ne F H₀ H₁ hz₀ hz₁] at he
  exact (mul_eq_zero.mp he).resolve_left
    (mul_ne_zero (pow_ne_zero 2 hz₀) (pow_ne_zero 2 (sub_ne_zero.mpr hz₁)))

/-- The same scalar criterion with the ordinary-point hypothesis given
as analyticity on the punctured affine domain. -/
theorem cubic_eq_zero_of_analyticOnNhd {F H₀ H₁ Hinf : ℂ → ℂ}
    (hF : AnalyticOnNhd ℂ F {z : ℂ | z ≠ 0 ∧ z ≠ 1})
    (hH₀ : AnalyticAt ℂ H₀ 0) (hH₁ : AnalyticAt ℂ H₁ 1)
    (hHinf : AnalyticAt ℂ Hinf 0)
    (h₀ : F =ᶠ[𝓝[≠] (0 : ℂ)] fun z => H₀ z / z ^ 2)
    (h₁ : F =ᶠ[𝓝[≠] (1 : ℂ)] fun z => H₁ z / (z - 1) ^ 2)
    (hinf : F =ᶠ[cocompact ℂ] fun z => z⁻¹ ^ 5 * Hinf z⁻¹) :
    EqOn F (fun _ => 0) {z : ℂ | z ≠ 0 ∧ z ≠ 1} := by
  intro z hz
  exact cubic_eq_zero_of_pole_germs (fun w hw₀ hw₁ => hF w ⟨hw₀, hw₁⟩)
    hH₀ hH₁ hHinf h₀ h₁ hinf hz.1 hz.2

end Wikipedia.HopfProblem.TriangleHolomorphicDifferentialsSphere
