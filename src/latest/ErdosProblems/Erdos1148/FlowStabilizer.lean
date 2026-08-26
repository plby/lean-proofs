import ErdosProblems.Erdos1148.RealFlow

/-!
# The stabilizer of the split binary quadratic form

In `SL₂(ℝ)`, the stabilizer of `xy` consists of the diagonal flow and
its negatives. The two signs have the same image modulo `SL₂(ℤ)`.
-/

namespace Erdos1148.DukeArithmetic

open scoped MatrixGroups

lemma formAction_splitForm_coefficients (g : SL(2, ℝ)) :
    formAction g (splitForm ℝ) =
      (-(g 1 1 * g 1 0), g 1 1 * g 0 0 + g 0 1 * g 1 0, -(g 0 1 * g 0 0)) := by
  simp only [formAction, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
  ext <;> dsimp [transform, splitForm] <;> ring

lemma offDiagonal_zero_of_fix_splitForm {g : SL(2, ℝ)}
    (h : formAction g (splitForm ℝ) = splitForm ℝ) : g 0 1 = 0 ∧ g 1 0 = 0 := by
  rw [formAction_splitForm_coefficients] at h
  have ha := congrArg Prod.fst h
  have hb := congrArg (fun v : ℝ × ℝ × ℝ => v.2.1) h
  have hc := congrArg (fun v : ℝ × ℝ × ℝ => v.2.2) h
  dsimp [splitForm] at ha hb hc
  have hdet := Matrix.SpecialLinearGroup.det_coe g
  rw [Matrix.det_fin_two] at hdet
  have had : g 0 0 * g 1 1 = 1 := by nlinarith
  have hα : g 0 0 ≠ 0 := fun hα => by rw [hα, zero_mul] at had; norm_num at had
  have hδ : g 1 1 ≠ 0 := fun hδ => by rw [hδ, mul_zero] at had; norm_num at had
  constructor
  · exact (mul_eq_zero.mp (neg_eq_zero.mp hc)).resolve_right hα
  · exact (mul_eq_zero.mp (neg_eq_zero.mp ha)).resolve_left hδ

lemma exists_signed_diagonalFlow_of_offDiagonal_zero {g : SL(2, ℝ)}
    (h01 : g 0 1 = 0) (h10 : g 1 0 = 0) :
    ∃ t : ℝ, g = diagonalFlow t ∨ g = -diagonalFlow t := by
  have hdet := Matrix.SpecialLinearGroup.det_coe g
  rw [Matrix.det_fin_two, h01, zero_mul, sub_zero] at hdet
  have hα : g 0 0 ≠ 0 := fun hα => by rw [hα, zero_mul] at hdet; norm_num at hdet
  have h11 : g 1 1 = (g 0 0)⁻¹ := by
    apply (mul_left_cancel₀ hα)
    rw [hdet, mul_inv_cancel₀ hα]
  rcases hα.lt_or_gt with hneg | hpos
  · refine ⟨2 * Real.log (-g 0 0), Or.inr ?_⟩
    have he : Real.exp ((2 * Real.log (-g 0 0)) / 2) = -g 0 0 := by
      rw [show (2 * Real.log (-g 0 0)) / 2 = Real.log (-g 0 0) by ring]
      exact Real.exp_log (by linarith)
    have he' : Real.exp (-((2 * Real.log (-g 0 0)) / 2)) = -(g 0 0)⁻¹ := by
      rw [Real.exp_neg, he, inv_neg]
    apply Subtype.ext
    change g.1 = -!![Real.exp ((2 * Real.log (-g 0 0)) / 2), 0;
      0, Real.exp (-((2 * Real.log (-g 0 0)) / 2))]
    rw [he, he']
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h01, h10, h11]
  · refine ⟨2 * Real.log (g 0 0), Or.inl ?_⟩
    have he : Real.exp ((2 * Real.log (g 0 0)) / 2) = g 0 0 := by
      rw [show (2 * Real.log (g 0 0)) / 2 = Real.log (g 0 0) by ring]
      exact Real.exp_log hpos
    have he' : Real.exp (-((2 * Real.log (g 0 0)) / 2)) = (g 0 0)⁻¹ := by
      rw [Real.exp_neg, he]
    apply Subtype.ext
    change g.1 = !![Real.exp ((2 * Real.log (g 0 0)) / 2), 0;
      0, Real.exp (-((2 * Real.log (g 0 0)) / 2))]
    rw [he, he']
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h01, h10, h11]

theorem exists_signed_diagonalFlow_of_fix_splitForm {g : SL(2, ℝ)}
    (h : formAction g (splitForm ℝ) = splitForm ℝ) :
    ∃ t : ℝ, g = diagonalFlow t ∨ g = -diagonalFlow t := by
  obtain ⟨h01, h10⟩ := offDiagonal_zero_of_fix_splitForm h
  exact exists_signed_diagonalFlow_of_offDiagonal_zero h01 h10

theorem exists_signed_flow_of_formAction_eq {g h : SL(2, ℝ)}
    (heq : formAction g (splitForm ℝ) = formAction h (splitForm ℝ)) :
    ∃ t : ℝ, h = g * diagonalFlow t ∨ h = -(g * diagonalFlow t) := by
  have hfix : formAction (g⁻¹ * h) (splitForm ℝ) = splitForm ℝ := by
    rw [formAction_mul, ← heq, ← formAction_mul, inv_mul_cancel, formAction_one]
  obtain ⟨t, ht | ht⟩ := exists_signed_diagonalFlow_of_fix_splitForm hfix
  · refine ⟨t, Or.inl ?_⟩
    simpa only [← mul_assoc, mul_inv_cancel, one_mul] using congrArg (fun k => g * k) ht
  · refine ⟨t, Or.inr ?_⟩
    simpa only [← mul_assoc, mul_inv_cancel, one_mul, mul_neg] using congrArg (fun k => g * k) ht

end Erdos1148.DukeArithmetic
