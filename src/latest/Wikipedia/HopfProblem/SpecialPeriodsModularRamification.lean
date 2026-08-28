import Wikipedia.HopfProblem.SpecialPeriodsModular
import Wikipedia.HopfProblem.SpecialPeriodsModularOrders
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic

/-!
# The critical values and exact ramification orders of j

The Ramanujan identities for the actual Eisenstein series give
`j' = -2πi E₄² E₆ / Δ`.  Consequently the only critical values are zero and
1728.  Every zero of `j` has order three and every zero of `j - 1728` has
order two.  These are genuine complex analytic orders, and are not assumed
as part of an abstract modular-cover structure.
-/

noncomputable section

open Function Filter Topology UpperHalfPlane ModularForm
open scoped ContDiff Manifold MatrixGroups

namespace Wikipedia.HopfProblem.SpecialPeriods

theorem discriminant_analyticAt (z : ℍ) :
    AnalyticAt ℂ (ModularForm.discriminant ∘ ofComplex) (z : ℂ) :=
  modularForm_analyticAt (CuspForm.discriminant : ModularForm 𝒮ℒ 12) z

/-- The actual complex derivative of j, with the conventional normalization. -/
theorem deriv_modularJ (z : ℍ) :
    deriv (modularJ ∘ ofComplex) (z : ℂ) =
      -(2 * (Real.pi : ℂ) * Complex.I) * (E₄ z ^ 2 * E₆ z) / ModularForm.discriminant z := by
  have h₄ := (modularForm_analyticAt E₄ z).differentiableAt.hasDerivAt
  have hΔ := (discriminant_analyticAt z).differentiableAt.hasDerivAt
  have hd := (h₄.pow 3).div hΔ (by
    simpa only [Function.comp_apply, ofComplex_apply] using discriminant_ne_zero z)
  have he := hd.deriv
  change deriv (modularJ ∘ ofComplex) (z : ℂ) = _ at he
  rw [he]
  simp only [Pi.pow_apply, Function.comp_apply, ofComplex_apply, Nat.cast_ofNat, Nat.reduceSub]
  rw [deriv_E₄, deriv_discriminant]
  field_simp [discriminant_ne_zero z]
  ring

/-- No critical value is hidden among the ordinary points of the base. -/
theorem deriv_modularJ_eq_zero_iff (z : ℍ) :
    deriv (modularJ ∘ ofComplex) (z : ℂ) = 0 ↔ modularJ z = 0 ∨ modularJ z = 1728 := by
  rw [deriv_modularJ, modularJ_eq_zero_iff, modularJ_eq_1728_iff]
  simp [discriminant_ne_zero z]

theorem deriv_modularJ_ne_zero (z : ℍ) (h₀ : modularJ z ≠ 0) (h₁ : modularJ z ≠ 1728) :
    deriv (modularJ ∘ ofComplex) (z : ℂ) ≠ 0 := by
  exact fun he => ((deriv_modularJ_eq_zero_iff z).mp he).elim h₀ h₁

theorem discriminant_inv_order_zero (z : ℍ) :
    analyticOrderAt (ModularForm.discriminant ∘ ofComplex)⁻¹ (z : ℂ) = 0 := by
  have hΔ := (discriminant_analyticAt z).inv (by
    simpa only [Function.comp_apply, ofComplex_apply] using discriminant_ne_zero z)
  apply hΔ.analyticOrderAt_eq_zero.mpr
  simpa only [Pi.inv_apply, Function.comp_apply, ofComplex_apply] using
    inv_ne_zero (discriminant_ne_zero z)

/-- Every preimage of zero has analytic order exactly three. -/
theorem analyticOrderAt_modularJ_of_eq_zero (z : ℍ) (hz : modularJ z = 0) :
    analyticOrderAt (modularJ ∘ ofComplex) (z : ℂ) = 3 := by
  have h₄ := modularForm_analyticAt E₄ z
  have hΔ := (discriminant_analyticAt z).inv (by
    simpa only [Function.comp_apply, ofComplex_apply] using discriminant_ne_zero z)
  change analyticOrderAt (((E₄ ∘ ofComplex) ^ 3) * (ModularForm.discriminant ∘ ofComplex)⁻¹)
    (z : ℂ) = 3
  rw [analyticOrderAt_mul (h₄.pow 3) hΔ, analyticOrderAt_pow h₄,
    discriminant_inv_order_zero,
    analyticOrderAt_E₄_of_eq_zero z ((modularJ_eq_zero_iff z).mp hz)]
  norm_num

/-- Every preimage of 1728 has analytic order exactly two after subtracting
that value. -/
theorem analyticOrderAt_modularJ_sub_1728_of_eq (z : ℍ) (hz : modularJ z = 1728) :
    analyticOrderAt (fun w : ℂ => modularJ (ofComplex w) - 1728) (z : ℂ) = 2 := by
  have h₆ := modularForm_analyticAt E₆ z
  have hΔ := (discriminant_analyticAt z).inv (by
    simpa only [Function.comp_apply, ofComplex_apply] using discriminant_ne_zero z)
  simp_rw [modularJ_sub_1728, div_eq_mul_inv]
  change analyticOrderAt (((E₆ ∘ ofComplex) ^ 2) * (ModularForm.discriminant ∘ ofComplex)⁻¹)
    (z : ℂ) = 2
  rw [analyticOrderAt_mul (h₆.pow 2) hΔ, analyticOrderAt_pow h₆,
    discriminant_inv_order_zero,
    analyticOrderAt_E₆_of_eq_zero z ((modularJ_eq_1728_iff z).mp hz)]
  norm_num

theorem analyticOrderAt_modularJ_rhoPoint :
    analyticOrderAt (modularJ ∘ ofComplex) rho = 3 :=
  analyticOrderAt_modularJ_of_eq_zero rhoPoint modularJ_rhoPoint

theorem analyticOrderAt_modularJ_sub_1728_I :
    analyticOrderAt (fun w : ℂ => modularJ (ofComplex w) - 1728) Complex.I = 2 :=
  analyticOrderAt_modularJ_sub_1728_of_eq UpperHalfPlane.I modularJ_I

/-- At every other point, the shifted function has an ordinary simple zero. -/
theorem analyticOrderAt_modularJ_sub_value_of_regular (z : ℍ)
    (h₀ : modularJ z ≠ 0) (h₁ : modularJ z ≠ 1728) :
    analyticOrderAt (fun w : ℂ => modularJ (ofComplex w) - modularJ z) (z : ℂ) = 1 := by
  simpa only [Function.comp_apply, ofComplex_apply] using
    (modularJ_analyticAt z).analyticOrderAt_sub_eq_one_of_deriv_ne_zero
      (deriv_modularJ_ne_zero z h₀ h₁)

/-- The complex inverse-function theorem supplies a genuine local inverse
near each regular value, rather than merely a nonzero-Jacobian predicate. -/
def modularLocalInverse (z : ℍ) (h₀ : modularJ z ≠ 0) (h₁ : modularJ z ≠ 1728) : ℂ → ℂ :=
  (modularJ_analyticAt z).hasStrictDerivAt.localInverse
    (modularJ ∘ ofComplex) (deriv (modularJ ∘ ofComplex) (z : ℂ)) (z : ℂ)
    (deriv_modularJ_ne_zero z h₀ h₁)

theorem modularLocalInverse_analyticAt (z : ℍ) (h₀ : modularJ z ≠ 0)
    (h₁ : modularJ z ≠ 1728) : AnalyticAt ℂ (modularLocalInverse z h₀ h₁) (modularJ z) := by
  simpa only [modularLocalInverse, Function.comp_apply, ofComplex_apply] using
    (modularJ_analyticAt z).analyticAt_localInverse (deriv_modularJ_ne_zero z h₀ h₁)

theorem modularLocalInverse_eventually_left_inverse (z : ℍ) (h₀ : modularJ z ≠ 0)
    (h₁ : modularJ z ≠ 1728) :
    ∀ᶠ w in 𝓝 (z : ℂ), modularLocalInverse z h₀ h₁ (modularJ (ofComplex w)) = w :=
  (modularJ_analyticAt z).hasStrictDerivAt.eventually_left_inverse
    (deriv_modularJ_ne_zero z h₀ h₁)

theorem modularLocalInverse_eventually_right_inverse (z : ℍ) (h₀ : modularJ z ≠ 0)
    (h₁ : modularJ z ≠ 1728) :
    ∀ᶠ w in 𝓝 (modularJ z), modularJ (ofComplex (modularLocalInverse z h₀ h₁ w)) = w := by
  simpa only [modularLocalInverse, Function.comp_apply, ofComplex_apply] using
    (modularJ_analyticAt z).hasStrictDerivAt.eventually_right_inverse
      (deriv_modularJ_ne_zero z h₀ h₁)

end Wikipedia.HopfProblem.SpecialPeriods
