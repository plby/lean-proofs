import ErdosProblems.Erdos1148.QuadraticOrderBasis

/-! # Recovering an integral form from the matrix of an order generator -/

namespace Erdos1148.DukeArithmetic

def orderRootMatrix (d : ℤ) (M : Matrix (Fin 2) (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  (2 : ℤ) • M - d • 1

lemma orderRootMatrix_apply (d : ℤ) (M : Matrix (Fin 2) (Fin 2) ℤ) (i j : Fin 2) :
    orderRootMatrix d M i j = 2 * M i j - d * if i = j then 1 else 0 := by
  change (2 : ℤ) • M i j - d • (1 : Matrix (Fin 2) (Fin 2) ℤ) i j = _
  rw [zsmul_eq_mul, zsmul_eq_mul, Matrix.one_apply]
  norm_cast

def formOfOrderMatrix (d : ℤ) (M : Matrix (Fin 2) (Fin 2) ℤ) : ℤ × ℤ × ℤ :=
  (M 1 0, d - 2 * M 0 0, -M 0 1)

lemma orderRootMatrix_square_entry {d : ℤ} {M : Matrix (Fin 2) (Fin 2) ℤ}
    (hM : orderRootMatrix d M * orderRootMatrix d M = d • (1 : Matrix (Fin 2) (Fin 2) ℤ)) :
    (2 * M 0 0 - d) ^ 2 + 4 * M 0 1 * M 1 0 = d := by
  have h := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℤ => A 0 0) hM
  simp only [Matrix.mul_apply, Fin.sum_univ_two, orderRootMatrix_apply,
    Matrix.smul_apply] at h
  norm_num at h
  linear_combination h

lemma formOfOrderMatrix_discr {d : ℤ} {M : Matrix (Fin 2) (Fin 2) ℤ}
    (hM : orderRootMatrix d M * orderRootMatrix d M = d • (1 : Matrix (Fin 2) (Fin 2) ℤ)) :
    discr (formOfOrderMatrix d M) = d := by
  dsimp [discr, formOfOrderMatrix]
  linear_combination orderRootMatrix_square_entry hM

lemma formOfOrderMatrix_fst_ne_zero {d : ℤ} (hns : ¬IsSquare d)
    {M : Matrix (Fin 2) (Fin 2) ℤ}
    (hM : orderRootMatrix d M * orderRootMatrix d M = d • (1 : Matrix (Fin 2) (Fin 2) ℤ)) :
    (formOfOrderMatrix d M).1 ≠ 0 :=
  fst_ne_zero_of_nonsquare_discr hns (formOfOrderMatrix_discr hM)

lemma trace_of_orderRootMatrix_square {d : ℤ} (hns : ¬IsSquare d)
    {M : Matrix (Fin 2) (Fin 2) ℤ}
    (hM : orderRootMatrix d M * orderRootMatrix d M = d • (1 : Matrix (Fin 2) (Fin 2) ℤ)) :
    M 0 0 + M 1 1 = d := by
  have h := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℤ => A 1 0) hM
  simp only [Matrix.mul_apply, Fin.sum_univ_two, orderRootMatrix_apply,
    Matrix.smul_apply] at h
  norm_num at h
  have hprod : M 1 0 * (M 0 0 + M 1 1 - d) = 0 := by nlinarith [h]
  have hn : M 1 0 ≠ 0 := formOfOrderMatrix_fst_ne_zero hns hM
  have hz := (mul_eq_zero.mp hprod).resolve_left hn
  omega

theorem formRootMatrix_formOfOrderMatrix {d : ℤ} (hns : ¬IsSquare d)
    {M : Matrix (Fin 2) (Fin 2) ℤ}
    (hM : orderRootMatrix d M * orderRootMatrix d M = d • (1 : Matrix (Fin 2) (Fin 2) ℤ)) :
    formRootMatrix (formOfOrderMatrix d M) = orderRootMatrix d M := by
  have htr := trace_of_orderRootMatrix_square hns hM
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [formRootMatrix, pellFormMatrix, formOfOrderMatrix, orderRootMatrix_apply] <;> omega

end Erdos1148.DukeArithmetic
