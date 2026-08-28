import Wikipedia.HopfProblem.SpecialPeriodsGlobalTauNormalizationDerivatives
import Mathlib.NumberTheory.Modular

/-!
# The actual modular centralizer of the unit cusp translation

An integral Möbius transformation commuting with translation by `-1`
must itself be an integer translation.  Equality of the projective
actions first gives a possible central sign between the conjugated
translation and the original one.  Their trace is `2`, so the negative
sign is impossible.  The exact matrix commutation forces the lower-left
entry to vanish, and integrality with determinant one gives the result.
-/

noncomputable section

open Function Set Matrix ModularGroup UpperHalfPlane
open scoped MatrixGroups

namespace Wikipedia.HopfProblem.SpecialPeriods

/-- Projective commutation with the unit translation is already exact
matrix commutation, since its nonzero trace excludes the central sign. -/
theorem modularSL_commutes_T_inv_of_actions_commute (γ : SL(2, ℤ))
    (h : ∀ z : ℍ, γ • (T⁻¹ • z) = T⁻¹ • (γ • z)) : Commute γ T⁻¹ := by
  have hconj : ∀ z : ℍ, (γ * T⁻¹ * γ⁻¹) • z = T⁻¹ • z := by
    intro z
    simp only [mul_smul]
    rw [h, smul_inv_smul]
  rcases (modularSL_actions_eq_iff (γ * T⁻¹ * γ⁻¹) T⁻¹).mp hconj with he | he
  · change γ * T⁻¹ = T⁻¹ * γ
    have hm := congrArg (fun B : SL(2, ℤ) => B * γ) he
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using hm
  · have ht := congrArg (fun B : SL(2, ℤ) => Matrix.trace B.val) he
    rw [modularSL_trace_conjugate] at ht
    change Matrix.trace (T⁻¹ : SL(2, ℤ)).val =
      Matrix.trace (-((T⁻¹ : SL(2, ℤ)).val)) at ht
    have hT : Matrix.trace (T⁻¹ : SL(2, ℤ)).val = 2 := by decide
    rw [Matrix.trace_neg, hT] at ht
    norm_num at ht

private theorem modularSL_lower_left_zero_of_commutes_T_inv (γ : SL(2, ℤ))
    (h : Commute γ T⁻¹) : γ 1 0 = 0 := by
  have he := congrArg (fun B : SL(2, ℤ) => B 0 0) h.eq
  change (γ.val * (T⁻¹ : SL(2, ℤ)).val) 0 0 =
    ((T⁻¹ : SL(2, ℤ)).val * γ.val) 0 0 at he
  rw [ModularGroup.coe_T_inv] at he
  simp [Matrix.mul_apply, Fin.sum_univ_two] at he
  omega

/-- The centralizer of the actual negative unit translation acts by
literal integer translations on the original upper half-plane. -/
theorem modularSL_integer_translation_of_commutes_T_inv_action (γ : SL(2, ℤ))
    (h : ∀ z : ℍ, γ • (T⁻¹ • z) = T⁻¹ • (γ • z)) :
    ∃ n : ℤ, ∀ z : ℍ, γ • z = (n : ℝ) +ᵥ z := by
  have hc := modularSL_lower_left_zero_of_commutes_T_inv γ
    (modularSL_commutes_T_inv_of_actions_commute γ h)
  obtain ⟨n, hn⟩ := ModularGroup.exists_eq_T_zpow_of_c_eq_zero (g := γ) hc
  exact ⟨n, fun z => (hn z).trans (UpperHalfPlane.modular_T_zpow_smul z n)⟩

/-- The complete centralizer characterization at the level of the
actual Möbius actions. -/
theorem modularSL_actions_commute_T_inv_iff (γ : SL(2, ℤ)) :
    (∀ z : ℍ, γ • (T⁻¹ • z) = T⁻¹ • (γ • z)) ↔
      ∃ n : ℤ, ∀ z : ℍ, γ • z = (n : ℝ) +ᵥ z := by
  refine ⟨modularSL_integer_translation_of_commutes_T_inv_action γ, ?_⟩
  rintro ⟨n, hn⟩ z
  have hT (w : ℍ) : T⁻¹ • w = (-1 : ℝ) +ᵥ w := by
    simpa using UpperHalfPlane.modular_T_zpow_smul w (-1)
  rw [hn, hn]
  simp only [hT, vadd_vadd, add_comm]

/-- The integral translation ambiguity is unique. -/
theorem modularSL_unique_integer_translation_of_commutes_T_inv_action (γ : SL(2, ℤ))
    (h : ∀ z : ℍ, γ • (T⁻¹ • z) = T⁻¹ • (γ • z)) :
    ∃! n : ℤ, ∀ z : ℍ, γ • z = (n : ℝ) +ᵥ z := by
  obtain ⟨n, hn⟩ := modularSL_integer_translation_of_commutes_T_inv_action γ h
  refine ⟨n, hn, fun m hm => ?_⟩
  have he : (m : ℝ) +ᵥ UpperHalfPlane.I = (n : ℝ) +ᵥ UpperHalfPlane.I :=
    (hm UpperHalfPlane.I).symm.trans (hn UpperHalfPlane.I)
  have he' : (m : ℝ) = (n : ℝ) :=
    (UpperHalfPlane.vadd_right_cancel_iff UpperHalfPlane.I).mp he
  exact_mod_cast he'

/-- The exact integral matrices in this projective centralizer are the
integer powers of `T` and their central negatives. -/
theorem modularSL_centralizer_T_inv_classification (γ : SL(2, ℤ))
    (h : ∀ z : ℍ, γ • (T⁻¹ • z) = T⁻¹ • (γ • z)) :
    ∃ n : ℤ, γ = T ^ n ∨ γ = -(T ^ n) := by
  obtain ⟨n, hn⟩ := modularSL_integer_translation_of_commutes_T_inv_action γ h
  refine ⟨n, (modularSL_actions_eq_iff γ (T ^ n)).mp ?_⟩
  intro z
  exact (hn z).trans (UpperHalfPlane.modular_T_zpow_smul z n).symm

/-- The same normalized ambiguity in the ordinary complex coordinate. -/
theorem modularSL_integer_translation_coe_of_commutes_T_inv_action (γ : SL(2, ℤ))
    (h : ∀ z : ℍ, γ • (T⁻¹ • z) = T⁻¹ • (γ • z)) :
    ∃ n : ℤ, ∀ z : ℍ, ((γ • z : ℍ) : ℂ) = (z : ℂ) + (n : ℂ) := by
  obtain ⟨n, hn⟩ := modularSL_integer_translation_of_commutes_T_inv_action γ h
  refine ⟨n, fun z => ?_⟩
  rw [hn z, UpperHalfPlane.coe_vadd]
  simp [add_comm]

end Wikipedia.HopfProblem.SpecialPeriods
