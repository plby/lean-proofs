import Wikipedia.HopfProblem.SpecialPeriodsGlobalTauNormalization
import Wikipedia.HopfProblem.SpecialPeriodsTriangleCuspStabilizer

/-!
# Derivatives and projective signs in integral modular normalization

At an actual upper-half-plane fixed point, multiplier `-1` is equivalent
to trace zero for a determinant-one real matrix.  The same statement for
integral matrices connects the analytic elliptic multiplier to the
integer classification used in the simultaneous normalization.

Equality of actual integral Möbius actions determines the matrix up to
its central sign.  Hence the parabolic trace condition passes through
the equality of the actual cusp actions, as well as through inversion
and conjugation.
-/

noncomputable section

open Function Set Matrix UpperHalfPlane
open scoped MatrixGroups

namespace Wikipedia.HopfProblem.SpecialPeriods

/-- The actual fixed-point multiplier is `-1` precisely when the real
determinant-one matrix has trace zero. -/
theorem realSL_fixed_multiplier_eq_neg_one_iff_trace_zero (B : SL(2, ℝ))
    (b : ℍ) (hfix : B • b = b) :
    Triangle.slMultiplier B b = -1 ↔ Matrix.trace B.val = 0 := by
  have hd := Triangle.slDenom_ne_zero B b
  have hidentity := Triangle.sl_fixed_denominator_identity B b hfix
  constructor
  · intro hmul
    have hsquare : Triangle.slDenom B b ^ 2 = -1 := by
      have he := (div_eq_iff (pow_ne_zero 2 hd)).mp hmul
      linear_combination he
    have hproduct : ((B 0 0 : ℂ) + (B 1 1 : ℂ)) * Triangle.slDenom B b = 0 := by
      dsimp [Triangle.slDenom] at hidentity hsquare ⊢
      linear_combination hidentity + hsquare
    have hsum := (mul_eq_zero.mp hproduct).resolve_right hd
    rw [Matrix.trace_fin_two]
    exact_mod_cast hsum
  · intro htrace
    rw [Matrix.trace_fin_two] at htrace
    have hsum : (B 0 0 : ℂ) + (B 1 1 : ℂ) = 0 := by exact_mod_cast htrace
    have hsquare : Triangle.slDenom B b ^ 2 = -1 := by
      dsimp [Triangle.slDenom] at hidentity ⊢
      linear_combination -hidentity + ((B 1 0 : ℂ) * (b : ℂ) + (B 1 1 : ℂ)) * hsum
    rw [Triangle.slMultiplier, hsquare]
    norm_num

/-- The fixed-point criterion expressed with the ordinary complex
derivative of the actual upper-half-plane Möbius action. -/
theorem realSL_fixed_deriv_eq_neg_one_iff_trace_zero (B : SL(2, ℝ))
    (b : ℍ) (hfix : B • b = b) :
    deriv (fun z : ℂ => ((B • ofComplex z : ℍ) : ℂ)) (b : ℂ) = -1 ↔
      Matrix.trace B.val = 0 := by
  rw [Triangle.sl_deriv_smul]
  exact realSL_fixed_multiplier_eq_neg_one_iff_trace_zero B b hfix

/-- The analytic elliptic multiplier gives the exact integer trace
condition, without assuming that the fixed point has already become `i`. -/
theorem modularSL_fixed_deriv_eq_neg_one_iff_trace_zero (B : SL(2, ℤ))
    (b : ℍ) (hfix : B • b = b) :
    deriv (fun z : ℂ => ((B • ofComplex z : ℍ) : ℂ)) (b : ℂ) = -1 ↔
      Matrix.trace B.val = 0 := by
  have hfixR : SpecialLinearGroup.map (Int.castRingHom ℝ) B • b = b := by
    rw [integerSL_real_action]
    exact hfix
  have htrace : Matrix.trace (SpecialLinearGroup.map (Int.castRingHom ℝ) B).val = 0 ↔
      Matrix.trace B.val = 0 := by
    rw [Matrix.trace_fin_two, Matrix.trace_fin_two]
    change (B 0 0 : ℝ) + (B 1 1 : ℝ) = 0 ↔ B 0 0 + B 1 1 = 0
    rw [← Int.cast_add, Int.cast_eq_zero]
  have h := (realSL_fixed_deriv_eq_neg_one_iff_trace_zero
    (SpecialLinearGroup.map (Int.castRingHom ℝ) B) b hfixR).trans htrace
  simpa only [integerSL_real_action] using h

theorem modularSL_trace_zero_of_fixed_deriv_neg_one (B : SL(2, ℤ))
    (b : ℍ) (hfix : B • b = b)
    (hderiv : deriv (fun z : ℂ => ((B • ofComplex z : ℍ) : ℂ)) (b : ℂ) = -1) :
    Matrix.trace B.val = 0 :=
  (modularSL_fixed_deriv_eq_neg_one_iff_trace_zero B b hfix).mp hderiv

theorem modularSL_trace_zero_of_fixed_hasDerivAt_neg_one (B : SL(2, ℤ))
    (b : ℍ) (hfix : B • b = b)
    (hderiv : HasDerivAt (fun z : ℂ => ((B • ofComplex z : ℍ) : ℂ)) (-1) (b : ℂ)) :
    Matrix.trace B.val = 0 :=
  modularSL_trace_zero_of_fixed_deriv_neg_one B b hfix hderiv.deriv

/-- Inversion preserves the trace of every determinant-one two-by-two
integral matrix. -/
theorem modularSL_trace_inv (B : SL(2, ℤ)) :
    Matrix.trace (B⁻¹).val = Matrix.trace B.val := by
  change Matrix.trace (Matrix.adjugate B.val) = Matrix.trace B.val
  simp [Matrix.trace_fin_two, Matrix.adjugate_fin_two, add_comm]

/-- An arbitrary integral change of modular coordinate preserves the
trace of the actual cusp matrix. -/
theorem modularSL_trace_conjugate (u B : SL(2, ℤ)) :
    Matrix.trace (u * B * u⁻¹).val = Matrix.trace B.val := by
  change Matrix.trace ((u : Matrix (Fin 2) (Fin 2) ℤ) * B.val *
    ((u⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) = _
  have hinv : ((u⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) *
      (u : Matrix (Fin 2) (Fin 2) ℤ) = 1 := by
    exact congrArg (fun C : SL(2, ℤ) => C.val) (inv_mul_cancel u)
  rw [Matrix.trace_mul_cycle, hinv, one_mul]

/-- Integral determinant-one matrices have the same upper-half-plane
action exactly when they differ by the central sign. -/
theorem modularSL_actions_eq_iff (B C : SL(2, ℤ)) :
    (∀ z : ℍ, B • z = C • z) ↔ B = C ∨ B = -C := by
  constructor
  · intro h
    have he : Triangle.realSLPermutation (B : SL(2, ℝ)) =
        Triangle.realSLPermutation (C : SL(2, ℝ)) := by
      apply Equiv.ext
      intro z
      change (SpecialLinearGroup.map (Int.castRingHom ℝ) B) • z =
        (SpecialLinearGroup.map (Int.castRingHom ℝ) C) • z
      simpa only [integerSL_real_action] using h z
    rcases (Triangle.realSLPermutation_eq_iff _ _).mp he with he | he
    · exact Or.inl (SpecialLinearGroup.map_intCast_injective (R := ℝ) he)
    · right
      apply SpecialLinearGroup.map_intCast_injective (R := ℝ)
      simpa only [SpecialLinearGroup.coe_int_neg] using he
  · rintro (rfl | rfl) z
    · rfl
    · exact ModularGroup.SL_neg_smul C z

/-- The square of the integral trace depends only on the actual
upper-half-plane action. -/
theorem modularSL_trace_sq_eq_of_actions_eq (B C : SL(2, ℤ))
    (h : ∀ z : ℍ, B • z = C • z) :
    Matrix.trace B.val ^ 2 = Matrix.trace C.val ^ 2 := by
  rcases (modularSL_actions_eq_iff B C).mp h with rfl | rfl
  · rfl
  · change Matrix.trace (-C.val) ^ 2 = Matrix.trace C.val ^ 2
    rw [Matrix.trace_neg, neg_sq]

/-- Parabolic trace values are unchanged when the same projective
action is represented by another integral lift. -/
theorem modularSL_trace_two_or_neg_two_of_actions_eq (B C : SL(2, ℤ))
    (h : ∀ z : ℍ, B • z = C • z)
    (hC : Matrix.trace C.val = 2 ∨ Matrix.trace C.val = -2) :
    Matrix.trace B.val = 2 ∨ Matrix.trace B.val = -2 := by
  rcases (modularSL_actions_eq_iff B C).mp h with rfl | rfl
  · exact hC
  · change Matrix.trace (-C.val) = 2 ∨ Matrix.trace (-C.val) = -2
    rw [Matrix.trace_neg]
    rcases hC with hC | hC
    · right
      rw [hC]
    · left
      rw [hC, neg_neg]

/-- Comparing the inverse action with an actual parabolic matrix also
gives the parabolic trace condition on the original matrix. -/
theorem modularSL_trace_two_or_neg_two_of_inverse_actions_eq (B C : SL(2, ℤ))
    (h : ∀ z : ℍ, B⁻¹ • z = C • z)
    (hC : Matrix.trace C.val = 2 ∨ Matrix.trace C.val = -2) :
    Matrix.trace B.val = 2 ∨ Matrix.trace B.val = -2 := by
  simpa only [modularSL_trace_inv] using
    modularSL_trace_two_or_neg_two_of_actions_eq B⁻¹ C h hC

/-- The actual cusp action relation yields exactly the product-trace
input required by the finite simultaneous-normalization theorem. -/
theorem modular_pair_trace_two_or_neg_two_of_cusp_actions_eq (B C : SL(2, ℤ))
    (h : ∀ z : ℍ, (triangleModularA * B)⁻¹ • z = C • z)
    (hC : Matrix.trace C.val = 2 ∨ Matrix.trace C.val = -2) :
    Matrix.trace (triangleModularA * B).val = 2 ∨
      Matrix.trace (triangleModularA * B).val = -2 :=
  modularSL_trace_two_or_neg_two_of_inverse_actions_eq (triangleModularA * B) C h hC

/-- An initial change of modular coordinate does not affect that cusp
trace input; the compared monodromy may be the actual conjugated cusp. -/
theorem modular_pair_trace_two_or_neg_two_of_conjugated_cusp_actions_eq
    (B C u : SL(2, ℤ))
    (h : ∀ z : ℍ, (triangleModularA * B)⁻¹ • z = (u * C * u⁻¹) • z)
    (hC : Matrix.trace C.val = 2 ∨ Matrix.trace C.val = -2) :
    Matrix.trace (triangleModularA * B).val = 2 ∨
      Matrix.trace (triangleModularA * B).val = -2 := by
  apply modular_pair_trace_two_or_neg_two_of_cusp_actions_eq B (u * C * u⁻¹) h
  simpa only [modularSL_trace_conjugate] using hC

end Wikipedia.HopfProblem.SpecialPeriods
