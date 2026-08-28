import Wikipedia.HomotopyGroupsOfSpheres.ComplexCliffordFive
import Wikipedia.HomotopyGroupsOfSpheres.ComplexMatrixRealification

/-! # The explicit Hermitian Clifford involution on the real four-sphere -/

noncomputable section

open scoped Matrix

namespace Wikipedia.HomotopyGroupsOfSpheres.CliffordFiveHermitian

abbrev Coordinates := Fin 5 → ℝ

def equator (v : Coordinates) : ComplexCrossProductUnitary.Vector :=
  ![(v 0 : ℂ) * Complex.I, (v 1 : ℂ) + (v 2 : ℂ) * Complex.I,
    (v 3 : ℂ) + (v 4 : ℂ) * Complex.I]

def matrix (v : Coordinates) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![v 0, 0, (v 2 : ℂ) + (v 1 : ℂ) * Complex.I, (v 4 : ℂ) + (v 3 : ℂ) * Complex.I;
     0, v 0, (v 4 : ℂ) - (v 3 : ℂ) * Complex.I, -(v 2 : ℂ) + (v 1 : ℂ) * Complex.I;
     (v 2 : ℂ) - (v 1 : ℂ) * Complex.I, (v 4 : ℂ) + (v 3 : ℂ) * Complex.I, -v 0, 0;
     (v 4 : ℂ) - (v 3 : ℂ) * Complex.I, -(v 2 : ℂ) - (v 1 : ℂ) * Complex.I, 0, -v 0]

theorem matrix_eq_clifford (v : Coordinates) :
    matrix v = (-Complex.I) • ComplexCliffordFive.matrix (equator v) := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    norm_num [matrix, equator, ComplexCliffordFive.matrix, Matrix.cons_val_two,
      Matrix.cons_val_three, Complex.mul_re, Complex.mul_im]

theorem matrix_hermitian (v : Coordinates) : (matrix v)ᴴ = matrix v := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    norm_num [matrix, Matrix.conjTranspose_apply, Matrix.cons_val_two, Matrix.cons_val_three]

theorem matrix_square (v : Coordinates) :
    matrix v * matrix v = ((∑ k, v k ^ 2 : ℝ) : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  have h3 : (2 : Fin 4).succ = 3 := rfl
  have h4 : (2 : Fin 3).succ.succ = 4 := rfl
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    norm_num [matrix, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.cons_val_two,
      Matrix.cons_val_three, pow_two, Complex.mul_re, Complex.mul_im, h3, h4] <;> ring

theorem matrix_trace (v : Coordinates) : (matrix v).trace = 0 := by
  simp [matrix, Matrix.trace, Fin.sum_univ_succ]

theorem continuous_matrix : Continuous matrix := by
  apply _root_.continuous_matrix
  intro i j
  fin_cases i <;> fin_cases j <;> simp only [matrix] <;> fun_prop

end Wikipedia.HomotopyGroupsOfSpheres.CliffordFiveHermitian
