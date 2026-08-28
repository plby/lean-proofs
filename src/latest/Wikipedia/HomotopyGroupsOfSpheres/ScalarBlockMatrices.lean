import Wikipedia.HomotopyGroupsOfSpheres.UnitaryZeroCorner

/-! # Two-by-two scalar matrices acting on two equal matrix blocks -/

noncomputable section

open scoped Matrix

namespace Wikipedia.HomotopyGroupsOfSpheres.ScalarBlockMatrices

variable {N : Type*} [DecidableEq N]

def matrix (A : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (N ⊕ N) (N ⊕ N) ℂ :=
  Matrix.fromBlocks (A 0 0 • 1) (A 0 1 • 1) (A 1 0 • 1) (A 1 1 • 1)

theorem matrix_mul [Fintype N] (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    matrix (N := N) (A * B) = matrix A * matrix B := by
  rw [matrix, matrix, matrix, Matrix.fromBlocks_multiply]
  apply Matrix.fromBlocks_inj.mpr
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.mul_smul,
    smul_smul, Matrix.mul_one, add_smul]
  simp [mul_comm]

theorem matrix_one : matrix (N := N) (1 : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
  simp [matrix, Matrix.fromBlocks_one]

theorem matrix_star (A : Matrix (Fin 2) (Fin 2) ℂ) :
    (matrix (N := N) A)ᴴ = matrix Aᴴ := by
  simp only [matrix, Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_one, Matrix.conjTranspose_apply]

theorem matrix_transpose (A : Matrix (Fin 2) (Fin 2) ℂ) :
    (matrix (N := N) A).transpose = matrix A.transpose := by
  simp only [matrix, Matrix.fromBlocks_transpose, Matrix.transpose_smul, Matrix.transpose_one,
    Matrix.transpose_apply]

theorem matrix_unitary [Fintype N] (U : unitary (Matrix (Fin 2) (Fin 2) ℂ)) :
    matrix (N := N) U.val ∈ unitary (Matrix (N ⊕ N) (N ⊕ N) ℂ) := by
  have hr : matrix (N := N) U.val * star (matrix U.val) = 1 := by
    change matrix U.val * (matrix (N := N) U.val)ᴴ = 1
    rw [matrix_star, ← matrix_mul]
    change matrix (N := N) (U.val * star U.val) = 1
    rw [U.property.2, matrix_one]
  exact ⟨mul_eq_one_comm.mp hr, hr⟩

def unitaryMap [Fintype N] :
    unitary (Matrix (Fin 2) (Fin 2) ℂ) →* unitary (Matrix (N ⊕ N) (N ⊕ N) ℂ) where
  toFun U := ⟨matrix U.val, matrix_unitary U⟩
  map_one' := Subtype.ext matrix_one
  map_mul' U V := Subtype.ext (matrix_mul U.val V.val)

theorem unitaryMap_val [Fintype N] (U : unitary (Matrix (Fin 2) (Fin 2) ℂ)) :
    (unitaryMap (N := N) U).val = matrix U.val := rfl

theorem continuous_matrix :
    Continuous (matrix (N := N) : Matrix (Fin 2) (Fin 2) ℂ → Matrix (N ⊕ N) (N ⊕ N) ℂ) := by
  apply _root_.continuous_matrix
  intro i j
  rcases i with i | i <;> rcases j with j | j
  all_goals
    simp only [matrix, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.smul_apply]
    fun_prop

theorem continuous_unitaryMap [Fintype N] : Continuous (unitaryMap (N := N)) :=
  (continuous_matrix.comp continuous_subtype_val).subtype_mk _

end Wikipedia.HomotopyGroupsOfSpheres.ScalarBlockMatrices
