import ErdosProblems.Erdos1148.IntegralFormEmbedding

/-! # Changes of form correspond to conjugation of the quadratic-field embedding -/

namespace Erdos1148.DukeArithmetic

open scoped MatrixGroups

lemma pellFormMatrix_formAction {R : Type*} [CommRing R] (g : SL(2, R))
    (t : R × R × R) (x y : R) :
    pellFormMatrix (formAction g t) x y =
      (g : Matrix (Fin 2) (Fin 2) R) * pellFormMatrix t x y * (g⁻¹ : SL(2, R)) := by
  have hdet := Matrix.SpecialLinearGroup.det_coe g
  rw [Matrix.det_fin_two] at hdet
  simp only [formAction, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_two] <;> dsimp [pellFormMatrix, transform]
  · linear_combination -x * hdet
  · ring
  · ring
  · linear_combination -x * hdet

theorem integralFormFieldEmbedding_action {d : ℤ} {t : ℤ × ℤ × ℤ}
    (ht : discr t = d) (γ : SL(2, ℤ)) (w : QuadraticDiscrAlgebra d) :
    integralFormFieldEmbedding ((discr_formAction γ t).trans ht) w =
      ((γ : SL(2, ℚ)) : Matrix (Fin 2) (Fin 2) ℚ) * integralFormFieldEmbedding ht w *
        ((γ : SL(2, ℚ))⁻¹ : SL(2, ℚ)) := by
  rw [integralFormFieldEmbedding_apply, integralFormFieldEmbedding_apply, mapCoeffs_formAction]
  exact pellFormMatrix_formAction _ _ _ _

end Erdos1148.DukeArithmetic
