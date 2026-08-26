import ErdosProblems.Erdos1148.FormAction
import ErdosProblems.Erdos1148.IsotropicDirections

/-!
# The real diagonal flow and mixed-coefficient separation

The diagonal flow fixes the split form `xy`. The mixed coefficient of two
translated split forms reads off the product of the off-diagonal entries
of their relative matrix. Integral mixed coefficients therefore give a
quantitative separation parameter for distinct form orbits.
-/

namespace Erdos1148.DukeArithmetic

open scoped MatrixGroups

noncomputable def diagonalFlow (t : ℝ) : SL(2, ℝ) :=
  ⟨!![Real.exp (t / 2), 0; 0, Real.exp (-(t / 2))], by
    simp [Matrix.det_fin_two, ← Real.exp_add]⟩

lemma diagonalFlow_zero : diagonalFlow 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diagonalFlow]

lemma diagonalFlow_add (s t : ℝ) : diagonalFlow (s + t) = diagonalFlow s * diagonalFlow t := by
  apply Subtype.ext
  change (diagonalFlow (s + t)).1 = (diagonalFlow s).1 * (diagonalFlow t).1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diagonalFlow, Matrix.mul_apply, Fin.sum_univ_two, add_div, Real.exp_add, mul_comm]

lemma diagonalFlow_neg (t : ℝ) : diagonalFlow (-t) = (diagonalFlow t)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← diagonalFlow_add, neg_add_cancel, diagonalFlow_zero]

lemma formAction_diagonalFlow (t : ℝ) (v : ℝ × ℝ × ℝ) :
    formAction (diagonalFlow t) v = (Real.exp (-t) * v.1, v.2.1, Real.exp t * v.2.2) := by
  rw [formAction, ← diagonalFlow_neg]
  dsimp [diagonalFlow, transform]
  have hneg : Real.exp (-(t / 2)) ^ 2 = Real.exp (-t) := by
    rw [pow_two, ← Real.exp_add]
    congr 1; ring
  have hpos : Real.exp (t / 2) ^ 2 = Real.exp t := by
    rw [pow_two, ← Real.exp_add]
    congr 1; ring
  simp [neg_div, hneg, hpos, ← Real.exp_add, mul_comm]

def splitForm (R : Type*) [CommRing R] : R × R × R := (0, 1, 0)

lemma discr_splitForm {R : Type*} [CommRing R] : discr (splitForm R) = 1 := by
  simp [splitForm, discr]

lemma formAction_diagonalFlow_splitForm (t : ℝ) :
    formAction (diagonalFlow t) (splitForm ℝ) = splitForm ℝ := by
  simp [formAction_diagonalFlow, splitForm]

lemma pairing_splitForm_action {R : Type*} [CommRing R] (g : SL(2, R)) :
    pairing (splitForm R) (formAction g (splitForm R)) = 2 + 4 * g 0 1 * g 1 0 := by
  have hdet := Matrix.SpecialLinearGroup.det_coe g
  rw [Matrix.det_fin_two] at hdet
  simp only [splitForm, formAction, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two,
    transform, pairing]
  dsimp
  linear_combination 2 * hdet

lemma pairing_relative_action {R : Type*} [CommRing R] (g h : SL(2, R)) :
    pairing (formAction g (splitForm R)) (formAction h (splitForm R)) =
      2 + 4 * (g⁻¹ * h) 0 1 * (g⁻¹ * h) 1 0 := by
  have heq := pairing_formAction g⁻¹ (formAction g (splitForm R)) (formAction h (splitForm R))
  rw [← formAction_mul, ← formAction_mul, inv_mul_cancel, formAction_one] at heq
  exact heq.symm.trans (pairing_splitForm_action (g⁻¹ * h))

lemma pairing_scaled_relative_action {R : Type*} [CommRing R]
    (g h : SL(2, R)) (ρ : R) :
    pairing (ρ • formAction g (splitForm R)) (ρ • formAction h (splitForm R)) =
      ρ ^ 2 * (2 + 4 * (g⁻¹ * h) 0 1 * (g⁻¹ * h) 1 0) := by
  rw [pairing_smul_smul, pairing_relative_action, pow_two]

lemma offDiagonal_product_lower_bound {d ℓ : ℤ} (hd : 0 < d) (hℓ : ℓ ≠ 2 * d)
    (β γ : ℝ) (hpair : (ℓ : ℝ) = (d : ℝ) * (2 + 4 * β * γ)) :
    1 / (4 * (d : ℝ)) ≤ |β * γ| := by
  have hne : ℓ - 2 * d ≠ 0 := sub_ne_zero.mpr hℓ
  have hpos : (0 : ℤ) < |ℓ - 2 * d| := abs_pos.mpr hne
  have hbound : (1 : ℤ) ≤ |ℓ - 2 * d| := by omega
  have hboundR : (1 : ℝ) ≤ |(ℓ : ℝ) - 2 * (d : ℝ)| := by exact_mod_cast hbound
  have heq : (ℓ : ℝ) - 2 * (d : ℝ) = (4 * (d : ℝ)) * (β * γ) := by
    linear_combination hpair
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have h4d : 0 < 4 * (d : ℝ) := by positivity
  rw [heq, abs_mul, abs_of_pos h4d] at hboundR
  exact (div_le_iff₀ h4d).mpr (by simpa only [mul_comm] using hboundR)

end Erdos1148.DukeArithmetic
