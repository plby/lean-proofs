import Wikipedia.HomotopyGroupsOfSpheres.RealUnitaryMatrices
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Complex.BigOperators

/-! # Explicit real block coordinates for complex matrices -/

noncomputable section

open scoped Matrix

namespace Wikipedia.HomotopyGroupsOfSpheres.ComplexMatrixRealification

variable {N : Type*}

def matrix (A : Matrix N N ℂ) : Matrix (N ⊕ N) (N ⊕ N) ℝ :=
  Matrix.fromBlocks (A.map Complex.re) (-A.map Complex.im)
    (A.map Complex.im) (A.map Complex.re)

theorem re_mul [Fintype N] (A B : Matrix N N ℂ) :
    (A * B).map Complex.re = A.map Complex.re * B.map Complex.re -
      A.map Complex.im * B.map Complex.im := by
  apply Matrix.ext
  intro i j
  simp [Matrix.mul_apply, Complex.mul_re, Complex.re_sum, Finset.sum_sub_distrib]

theorem im_mul [Fintype N] (A B : Matrix N N ℂ) :
    (A * B).map Complex.im = A.map Complex.re * B.map Complex.im +
      A.map Complex.im * B.map Complex.re := by
  apply Matrix.ext
  intro i j
  simp [Matrix.mul_apply, Complex.mul_im, Complex.im_sum, Finset.sum_add_distrib]

theorem matrix_mul [Fintype N] (A B : Matrix N N ℂ) : matrix (A * B) = matrix A * matrix B := by
  rw [matrix, matrix, matrix, Matrix.fromBlocks_multiply, re_mul, im_mul]
  apply Matrix.fromBlocks_inj.mpr
  simp [sub_eq_add_neg, add_comm]

theorem matrix_one [DecidableEq N] : matrix (1 : Matrix N N ℂ) = 1 := by
  apply Matrix.ext
  intro i j
  rcases i with i | i <;> rcases j with j | j
  all_goals simp [matrix, Matrix.one_apply, apply_ite]

theorem matrix_star (A : Matrix N N ℂ) : matrix Aᴴ = (matrix A).transpose := by
  apply Matrix.ext
  intro i j
  rcases i with i | i <;> rcases j with j | j
  all_goals simp [matrix, Matrix.conjTranspose_apply]

theorem matrix_trace [Fintype N] (A : Matrix N N ℂ) : (matrix A).trace = 2 * A.trace.re := by
  simp only [matrix, Matrix.trace, Fintype.sum_sum_type, Matrix.diag_apply,
    Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₂₂, Matrix.map_apply, Complex.re_sum]
  ring

theorem matrix_symmetric (A : Matrix N N ℂ) (hA : Aᴴ = A) :
    (matrix A).transpose = matrix A := by
  rw [← matrix_star, hA]

theorem matrix_square [Fintype N] [DecidableEq N] (A : Matrix N N ℂ) (hA : A * A = 1) :
    matrix A * matrix A = 1 := by
  rw [← matrix_mul, hA, matrix_one]

theorem continuous_matrix : Continuous (matrix : Matrix N N ℂ → Matrix (N ⊕ N) (N ⊕ N) ℝ) := by
  apply _root_.continuous_matrix
  intro i j
  rcases i with i | i <;> rcases j with j | j
  all_goals
    simp only [matrix, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.map_apply, Matrix.neg_apply]
    fun_prop

end Wikipedia.HomotopyGroupsOfSpheres.ComplexMatrixRealification
