import ErdosProblems.Erdos1148.PeriodGroup

/-! # The explicit Pell matrix associated with a diagonal-flow period -/

namespace Erdos1148.DukeArithmetic

open scoped MatrixGroups

lemma conjugate_split_diagonal (g : SL(2, ℝ)) (x y : ℝ) :
    (g : Matrix (Fin 2) (Fin 2) ℝ) * !![x + y, 0; 0, x - y] *
        (g⁻¹ : SL(2, ℝ)) =
      pellFormMatrix (formAction g (splitForm ℝ)) x (-y) := by
  have hdet := Matrix.SpecialLinearGroup.det_coe g
  rw [Matrix.det_fin_two] at hdet
  rw [formAction_splitForm_coefficients, Matrix.SpecialLinearGroup.coe_inv,
    Matrix.adjugate_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_two] <;> dsimp [pellFormMatrix]
  · linear_combination x * hdet
  · ring
  · ring
  · linear_combination x * hdet

lemma conjugate_diagonalFlow_pellFormMatrix (g : SL(2, ℝ)) (s : ℝ) :
    ((g * diagonalFlow s * g⁻¹ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) =
      pellFormMatrix (formAction g (splitForm ℝ)) (Real.cosh (s / 2)) (-Real.sinh (s / 2)) := by
  have hdiag : (diagonalFlow s : Matrix (Fin 2) (Fin 2) ℝ) =
      !![Real.cosh (s / 2) + Real.sinh (s / 2), 0;
        0, Real.cosh (s / 2) - Real.sinh (s / 2)] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      dsimp [diagonalFlow] <;> simp only [Real.cosh_eq, Real.sinh_eq] <;> ring
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hdiag]
  exact conjugate_split_diagonal g _ _

lemma pellFormMatrix_smul_div (t : ℝ × ℝ × ℝ) {ρ : ℝ} (hρ : ρ ≠ 0) (x y : ℝ) :
    pellFormMatrix (ρ • t) x (y / ρ) = pellFormMatrix t x y := by
  ext i j
  fin_cases i <;> fin_cases j <;> dsimp [pellFormMatrix] <;> field_simp

theorem integral_period_pellFormMatrix {d : ℤ} (hd : 0 < d) {t : ℤ × ℤ × ℤ}
    (g : SL(2, ℝ))
    (hg : Real.sqrt (d : ℝ) • formAction g (splitForm ℝ) = mapCoeffs (Int.castRingHom ℝ) t)
    (γ : SL(2, ℤ)) (s : ℝ) (hs : (γ : SL(2, ℝ)) * g = g * diagonalFlow s) :
    ((γ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) =
      pellFormMatrix (mapCoeffs (Int.castRingHom ℝ) t)
        (Real.cosh (s / 2)) (-Real.sinh (s / 2) / Real.sqrt (d : ℝ)) := by
  have hρ : Real.sqrt (d : ℝ) ≠ 0 :=
    (Real.sqrt_pos.mpr (by exact_mod_cast hd)).ne'
  have hγ : (γ : SL(2, ℝ)) = g * diagonalFlow s * g⁻¹ := by
    rw [← hs, mul_assoc, mul_inv_cancel, mul_one]
  rw [hγ, conjugate_diagonalFlow_pellFormMatrix, ← hg, pellFormMatrix_smul_div _ hρ]

end Erdos1148.DukeArithmetic
