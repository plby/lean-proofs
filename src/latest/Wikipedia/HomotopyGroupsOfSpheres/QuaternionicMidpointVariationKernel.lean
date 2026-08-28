import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicFirstColumnVariationComponents
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSymmetricCurveTangency

/-! # Kernel elimination for the full midpoint first-column variation

All tangent identities used here are derived from the actual symmetric
unitary curve. The determinant-one hypothesis is imposed on that curve,
not on an unrelated linear model.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicBottMatrix

open QuaternionicComplexPlane QuaternionicSymmetricMatrices ComplexCrossProductUnitary

theorem midpoint_curve_middle_tangent (B : ℝ → Space (Fin 3))
    (D : Matrix (Fin 3) (Fin 3) ℂ) (x : ℝ)
    (hB : ∀ r s, HasDerivAt (fun y ↦ (B y).val.val r s) (D r s) x)
    (u : unitary ℂ) (hBx : (B x).val.val = u.val • targetMatrix targetAlpha targetBeta) :
    D 1 1 + u.val ^ 2 * star (D 1 1) = 0 := by
  have he := unitary_curve_derivative B D x hB 1 1
  simp only [hBx, Fin.sum_univ_three, targetMatrix, Matrix.smul_apply, smul_eq_mul,
    Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two] at he
  have hu := u.property.2
  simp only [Complex.star_def] at he hu ⊢
  simp at he
  linear_combination u.val * he - D 1 1 * hu

theorem midpoint_curve_offdiag_tangent (B : ℝ → Space (Fin 3))
    (D : Matrix (Fin 3) (Fin 3) ℂ) (x : ℝ)
    (hB : ∀ r s, HasDerivAt (fun y ↦ (B y).val.val r s) (D r s) x)
    (u : unitary ℂ) (hBx : (B x).val.val = u.val • targetMatrix targetAlpha targetBeta) :
    D 2 1 + u.val ^ 2 * targetBeta * star (D 1 0) +
      u.val ^ 2 * targetAlpha * star (D 2 1) = 0 := by
  have he := unitary_curve_derivative B D x hB 1 2
  have h01 := symmetric_curve_derivative B D x hB 0 1
  have h12 := symmetric_curve_derivative B D x hB 1 2
  simp [hBx, Fin.sum_univ_three, targetMatrix, Matrix.cons_val_two, h01, h12] at he
  have hu := u.property.2
  simp only [Complex.star_def] at he hu ⊢
  linear_combination u.val * he - D 2 1 * hu

theorem midpoint_curve_outer_tangent (B : ℝ → Space (Fin 3))
    (D : Matrix (Fin 3) (Fin 3) ℂ) (x : ℝ)
    (hB : ∀ r s, HasDerivAt (fun y ↦ (B y).val.val r s) (D r s) x)
    (u : unitary ℂ) (hBx : (B x).val.val = u.val • targetMatrix targetAlpha targetBeta)
    (h00 : D 0 0 = targetAlpha * D 1 1) (h20 : D 2 0 = targetBeta * D 1 1) :
    D 2 2 = targetAlpha * D 1 1 := by
  have he := unitary_curve_derivative B D x hB 0 2
  have h02 := (symmetric_curve_derivative B D x hB 0 2).trans h20
  simp only [Fin.isValue, RCLike.star_def, hBx, targetMatrix, Matrix.smul_apply,
    Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_two, Nat.succ_eq_add_one,
    Nat.reduceAdd, Matrix.tail_cons, Matrix.head_cons, Matrix.cons_val_fin_one,
    smul_eq_mul, Matrix.cons_val_zero, star_mul', Fin.sum_univ_three, h00,
    map_mul, h02, Matrix.cons_val_one, mul_zero, map_zero, zero_mul, add_zero,
    h20, Matrix.head_fin_const] at he
  apply mul_left_cancel₀ (mul_ne_zero (star_ne_zero.mpr (unitary_complex_ne_zero u))
    targetBeta_ne_zero)
  simp only [Complex.star_def] at he ⊢
  have hα : (starRingEnd ℂ) targetAlpha = -targetAlpha := targetAlpha_star
  have hβ : (starRingEnd ℂ) targetBeta = targetBeta := targetBeta_star
  rw [hα, hβ] at he
  linear_combination he

theorem midpointColumnVariation_kernel_of_constant_det (B : ℝ → Space (Fin 3))
    (D : Matrix (Fin 3) (Fin 3) ℂ) (x : ℝ)
    (hB : ∀ r s, HasDerivAt (fun y ↦ (B y).val.val r s) (D r s) x)
    (c : ℂ) (hdet : ∀ y, (B y).val.val.det = c) (u : unitary ℂ)
    (hBx : (B x).val.val = u.val • targetMatrix targetAlpha targetBeta) (w : ℂ)
    (hv : ∀ r, midpointColumnVariation w u D r = 0) : w = 0 ∧ D = 0 := by
  have hsym := symmetric_curve_derivative B D x hB
  have h0 := congrArg coordinate (hv 0)
  have h1 := congrArg coordinate (hv 1)
  rw [midpointColumnVariation_coordinate_zero, hsym 0 1] at h0
  rw [midpointColumnVariation_coordinate_one] at h1
  change _ = (0 : ℂ) at h0 h1
  obtain ⟨hw, h10, h21⟩ := linearized_column_kernel u w (D 1 0) (D 2 1)
    (midpoint_curve_offdiag_tangent B D x hB u hBx) h0 h1
  have hm := midpoint_curve_middle_tangent B D x hB u hBx
  have hc0 : D 0 0 * star u.val + u.val * targetAlpha * star (D 1 1) = 0 := by
    have he := congrArg complexPart (hv 0)
    change _ = (0 : ℂ) at he
    simpa [midpointColumnVariation_complexPart, remainingRow, targetComplexColumn] using he
  have hc1 : D 2 0 * star u.val + u.val * targetBeta * star (D 1 1) = 0 := by
    have he := congrArg complexPart (hv 1)
    change _ = (0 : ℂ) at he
    simpa [midpointColumnVariation_complexPart, remainingRow, targetComplexColumn,
      Matrix.cons_val_two] using he
  have hu := u.property.1
  simp only [Complex.star_def] at hm hc0 hc1 hu
  have h00 : D 0 0 = targetAlpha * D 1 1 := by
    linear_combination u.val * hc0 - targetAlpha * hm - D 0 0 * hu
  have h20 : D 2 0 = targetBeta * D 1 1 := by
    linear_combination u.val * hc1 - targetBeta * hm - D 2 0 * hu
  have h02 := (hsym 0 2).trans h20
  have h22 := midpoint_curve_outer_tangent B D x hB u hBx h00 h20
  have hd := constant_curve_det_tangent_midpoint B D x hB c hdet u hBx
  rw [h00, h22, h02, h20] at hd
  have h11 : D 1 1 = 0 := by
    linear_combination -hd / 3 + (2 * D 1 1 / 3) * target_polynomial
  refine ⟨hw, ?_⟩
  apply Matrix.ext
  intro r s
  fin_cases r <;> fin_cases s <;>
    simp [h00, h02, h20, h22, h11, h10, h21, hsym 0 1, hsym 1 2]

theorem midpointColumnVariation_kernel (B : ℝ → Space (Fin 3))
    (D : Matrix (Fin 3) (Fin 3) ℂ) (x : ℝ)
    (hB : ∀ r s, HasDerivAt (fun y ↦ (B y).val.val r s) (D r s) x)
    (hdet : ∀ y, (B y).val.val.det = 1) (u : unitary ℂ)
    (hBx : (B x).val.val = u.val • targetMatrix targetAlpha targetBeta) (w : ℂ)
    (hv : ∀ r, midpointColumnVariation w u D r = 0) : w = 0 ∧ D = 0 :=
  midpointColumnVariation_kernel_of_constant_det B D x hB 1 hdet u hBx w hv

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicBottMatrix
