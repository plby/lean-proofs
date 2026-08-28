import Wikipedia.HopfProblem.SpecialPeriodsModularForms
import Wikipedia.HopfProblem.SpecialPeriodsSerreDerivative

/-!
# Simple elliptic zeros of the Eisenstein series

The Serre derivative raises the weight by two.  In weights six and eight, a
level-one modular form is determined by its constant Fourier coefficient.
This gives the two Ramanujan identities needed here.  Together with the
nonvanishing of the modular discriminant, these prove that the elliptic
zeros of the normalized Eisenstein series have order exactly one.
-/

noncomputable section

open UpperHalfPlane ModularForm EisensteinSeries Derivative
open scoped MatrixGroups Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods

/-- The first Ramanujan identity, in Serre-derivative form. -/
theorem serreDerivative_E₄ (z : ℍ) :
    serreDerivative 4 E₄ z = -(E₆ z) / 3 := by
  have heq : serreDerivativeModularForm E₄ = (-1 / 3 : ℂ) • E₆ := by
    apply levelOne_eq_of_qExpansion_coeff_zero (by norm_num)
    rw [serreDerivativeModularForm_qExpansion_coeff_zero,
      FunLike.coe_smul, ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL,
      PowerSeries.coeff_smul, E_qExpansion_coeff_zero _ ⟨2, rfl⟩,
      E_qExpansion_coeff_zero _ ⟨3, rfl⟩]
    norm_num
  have hz := congrArg (fun f : ModularForm 𝒮ℒ 6 => f z) heq
  change serreDerivative 4 E₄ z = (-1 / 3 : ℂ) * E₆ z at hz
  rw [hz]
  ring

/-- The second Ramanujan identity, in Serre-derivative form. -/
theorem serreDerivative_E₆ (z : ℍ) :
    serreDerivative 6 E₆ z = -(E₄ z ^ 2) / 2 := by
  have heq : serreDerivativeModularForm E₆ = (-1 / 2 : ℂ) • E₄.mul E₄ := by
    apply levelOne_eq_of_qExpansion_coeff_zero (by norm_num)
    rw [serreDerivativeModularForm_qExpansion_coeff_zero,
      FunLike.coe_smul, ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL,
      PowerSeries.coeff_smul, ModularForm.qExpansion_mul one_pos one_mem_strictPeriods_SL,
      PowerSeries.coeff_mul]
    norm_num [E_qExpansion_coeff_zero _ ⟨3, rfl⟩,
      E_qExpansion_coeff_zero _ ⟨2, rfl⟩]
  have hz := congrArg (fun f : ModularForm 𝒮ℒ 8 => f z) heq
  change serreDerivative 6 E₆ z = (-1 / 2 : ℂ) * (E₄ z * E₄ z) at hz
  rw [hz]
  ring

/-- Ramanujan's identity for the normalized derivative of `E₄`. -/
theorem normalizedDeriv_E₄ (z : ℍ) :
    normalizedDerivOfComplex E₄ z =
      (E2 z * E₄ z - E₆ z) / 3 := by
  have h := serreDerivative_E₄ z
  unfold serreDerivative at h
  linear_combination h

/-- Ramanujan's identity for the normalized derivative of `E₆`. -/
theorem normalizedDeriv_E₆ (z : ℍ) :
    normalizedDerivOfComplex E₆ z =
      (E2 z * E₆ z - E₄ z ^ 2) / 2 := by
  have h := serreDerivative_E₆ z
  unfold serreDerivative at h
  linear_combination h

/-- The normalized logarithmic derivative of the modular discriminant. -/
theorem normalizedDeriv_discriminant (z : ℍ) :
    normalizedDerivOfComplex ModularForm.discriminant z =
      E2 z * ModularForm.discriminant z := by
  have hf : ModularForm.discriminant =
      (1 / 1728 : ℂ) • ((E₄ : ℍ → ℂ) ^ 3 - (E₆ : ℍ → ℂ) ^ 2) := by
    funext w
    change ModularForm.discriminant w =
      (1 / 1728 : ℂ) * (E₄ w ^ 3 - E₆ w ^ 2)
    rw [discriminant_eq_E₄_cube_sub_E₆_sq]
    ring
  have h4 : MDiff (E₄ : ℍ → ℂ) := ModularFormClass.holo E₄
  have h6 : MDiff (E₆ : ℍ → ℂ) := ModularFormClass.holo E₆
  rw [hf, normalizedDerivOfComplex_smul _ _ ((h4.pow 3).sub (h6.pow 2)),
    normalizedDerivOfComplex_sub _ _ (h4.pow 3) (h6.pow 2),
    normalizedDerivOfComplex_pow _ 3 h4, normalizedDerivOfComplex_pow _ 2 h6]
  simp only [Pi.smul_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply,
    Pi.natCast_apply, smul_eq_mul]
  rw [normalizedDeriv_E₄, normalizedDeriv_E₆]
  ring

/-- Recover the ordinary derivative from its conventional normalization. -/
theorem deriv_eq_two_pi_I_mul_normalizedDeriv (f : ℍ → ℂ) (z : ℍ) :
    deriv (f ∘ ofComplex) (z : ℂ) =
      (2 * (Real.pi : ℂ) * Complex.I) * normalizedDerivOfComplex f z := by
  rw [normalizedDerivOfComplex, ← mul_assoc,
    mul_inv_cancel₀ Complex.two_pi_I_ne_zero, one_mul]

theorem deriv_E₄ (z : ℍ) :
    deriv (E₄ ∘ ofComplex) (z : ℂ) =
      (2 * (Real.pi : ℂ) * Complex.I) / 3 * (E2 z * E₄ z - E₆ z) := by
  rw [deriv_eq_two_pi_I_mul_normalizedDeriv, normalizedDeriv_E₄]
  ring

theorem deriv_E₆ (z : ℍ) :
    deriv (E₆ ∘ ofComplex) (z : ℂ) =
      (2 * (Real.pi : ℂ) * Complex.I) / 2 * (E2 z * E₆ z - E₄ z ^ 2) := by
  rw [deriv_eq_two_pi_I_mul_normalizedDeriv, normalizedDeriv_E₆]
  ring

theorem deriv_discriminant (z : ℍ) :
    deriv (ModularForm.discriminant ∘ ofComplex) (z : ℂ) =
      (2 * (Real.pi : ℂ) * Complex.I) * E2 z * ModularForm.discriminant z := by
  rw [deriv_eq_two_pi_I_mul_normalizedDeriv, normalizedDeriv_discriminant]
  ring

/-- Every zero of `E₄` in the upper half-plane has nonzero derivative. -/
theorem deriv_E₄_ne_zero_of_eq_zero (z : ℍ) (hz : E₄ z = 0) :
    deriv (E₄ ∘ ofComplex) (z : ℂ) ≠ 0 := by
  have h6 : E₆ z ≠ 0 := (E₄_E₆_not_both_zero z).resolve_left (by simp [hz])
  rw [deriv_E₄, hz, mul_zero, zero_sub]
  exact mul_ne_zero (div_ne_zero Complex.two_pi_I_ne_zero (by norm_num))
    (neg_ne_zero.mpr h6)

/-- Every zero of `E₆` in the upper half-plane has nonzero derivative. -/
theorem deriv_E₆_ne_zero_of_eq_zero (z : ℍ) (hz : E₆ z = 0) :
    deriv (E₆ ∘ ofComplex) (z : ℂ) ≠ 0 := by
  have h4 : E₄ z ≠ 0 := (E₄_E₆_not_both_zero z).resolve_right (by simp [hz])
  rw [deriv_E₆, hz, mul_zero, zero_sub]
  exact mul_ne_zero (div_ne_zero Complex.two_pi_I_ne_zero (by norm_num))
    (neg_ne_zero.mpr (pow_ne_zero 2 h4))

theorem analyticOrderAt_E₄_of_eq_zero (z : ℍ) (hz : E₄ z = 0) :
    analyticOrderAt (E₄ ∘ ofComplex) (z : ℂ) = 1 := by
  apply (modularForm_analyticAt E₄ z).analyticOrderAt_eq_one_of_zero_deriv_ne_zero
  · simpa only [Function.comp_apply, ofComplex_apply] using hz
  · exact deriv_E₄_ne_zero_of_eq_zero z hz

theorem analyticOrderAt_E₆_of_eq_zero (z : ℍ) (hz : E₆ z = 0) :
    analyticOrderAt (E₆ ∘ ofComplex) (z : ℂ) = 1 := by
  apply (modularForm_analyticAt E₆ z).analyticOrderAt_eq_one_of_zero_deriv_ne_zero
  · simpa only [Function.comp_apply, ofComplex_apply] using hz
  · exact deriv_E₆_ne_zero_of_eq_zero z hz

/-- The normalized derivative of `E₄` at the order-three elliptic point. -/
theorem normalizedDeriv_E₄_rhoPoint :
    normalizedDerivOfComplex E₄ rhoPoint = -(E₆ rhoPoint) / 3 := by
  simpa only [serreDerivative, E₄_rhoPoint, mul_zero, sub_zero] using
    serreDerivative_E₄ rhoPoint

/-- The normalized derivative of `E₆` at the order-two point of the modular
quotient (the order-four point before dividing by the center). -/
theorem normalizedDeriv_E₆_I :
    normalizedDerivOfComplex E₆ UpperHalfPlane.I = -(E₄ UpperHalfPlane.I ^ 2) / 2 := by
  simpa only [serreDerivative, E₆_I, mul_zero, sub_zero] using
    serreDerivative_E₆ UpperHalfPlane.I

theorem deriv_E₄_rhoPoint_ne_zero : deriv (E₄ ∘ ofComplex) rho ≠ 0 :=
  deriv_E₄_ne_zero_of_eq_zero rhoPoint E₄_rhoPoint

theorem deriv_E₆_I_ne_zero : deriv (E₆ ∘ ofComplex) Complex.I ≠ 0 :=
  deriv_E₆_ne_zero_of_eq_zero UpperHalfPlane.I E₆_I

/-- `E₄` has a simple zero at `ρ`, in the ordinary complex coordinate. -/
theorem analyticOrderAt_E₄_rhoPoint :
    analyticOrderAt (E₄ ∘ ofComplex) rho = 1 :=
  analyticOrderAt_E₄_of_eq_zero rhoPoint E₄_rhoPoint

/-- `E₆` has a simple zero at `i`, in the ordinary complex coordinate. -/
theorem analyticOrderAt_E₆_I :
    analyticOrderAt (E₆ ∘ ofComplex) Complex.I = 1 :=
  analyticOrderAt_E₆_of_eq_zero UpperHalfPlane.I E₆_I

end Wikipedia.HopfProblem.SpecialPeriods
