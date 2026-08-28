import Wikipedia.HomotopyGroupsOfSpheres.UnitaryZeroCorner

/-! # The actual unitary inclusion into the first of two equal blocks -/

noncomputable section

open scoped Matrix

namespace Wikipedia.HomotopyGroupsOfSpheres.UnitaryBlockDiagonal

variable {N : Type*} [DecidableEq N]

def matrix (A : Matrix N N ℂ) : Matrix (N ⊕ N) (N ⊕ N) ℂ := Matrix.fromBlocks A 0 0 1

theorem matrix_one : matrix (1 : Matrix N N ℂ) = 1 := Matrix.fromBlocks_one

theorem matrix_mul [Fintype N] (A B : Matrix N N ℂ) :
    matrix (A * B) = matrix A * matrix B := by
  simp [matrix, Matrix.fromBlocks_multiply]

theorem matrix_star (A : Matrix N N ℂ) : (matrix A)ᴴ = matrix Aᴴ := by
  simp [matrix, Matrix.fromBlocks_conjTranspose]

theorem matrix_unitary [Fintype N] (U : unitary (Matrix N N ℂ)) :
    matrix U.val ∈ unitary (Matrix (N ⊕ N) (N ⊕ N) ℂ) := by
  have hr : matrix U.val * star (matrix U.val) = 1 := by
    change matrix U.val * (matrix U.val)ᴴ = 1
    rw [matrix_star, ← matrix_mul]
    change matrix (U.val * star U.val) = 1
    rw [U.property.2, matrix_one]
  exact ⟨mul_eq_one_comm.mp hr, hr⟩

def inclusion [Fintype N] :
    unitary (Matrix N N ℂ) →* unitary (Matrix (N ⊕ N) (N ⊕ N) ℂ) where
  toFun U := ⟨matrix U.val, matrix_unitary U⟩
  map_one' := Subtype.ext matrix_one
  map_mul' U V := Subtype.ext (matrix_mul U.val V.val)

theorem inclusion_val [Fintype N] (U : unitary (Matrix N N ℂ)) :
    (inclusion U).val = matrix U.val := rfl

theorem continuous_matrix : Continuous (matrix (N := N)) := by
  apply _root_.continuous_matrix
  intro i j
  rcases i with i | i <;> rcases j with j | j
  · exact continuous_apply_apply i j
  all_goals exact continuous_const

theorem continuous_inclusion [Fintype N] : Continuous (inclusion (N := N)) :=
  (continuous_matrix.comp continuous_subtype_val).subtype_mk _

def inclusionMap [Fintype N] :
    C(unitary (Matrix N N ℂ), unitary (Matrix (N ⊕ N) (N ⊕ N) ℂ)) :=
  ⟨inclusion, continuous_inclusion⟩

theorem matrix_negativeSwap_product [Fintype N] (A : Matrix N N ℂ) :
    matrix A * Matrix.fromBlocks (0 : Matrix N N ℂ) (-1) (-1) 0 * (matrix A).transpose =
      Matrix.fromBlocks 0 (-A) (-A.transpose) 0 := by
  simp [matrix, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply]

end Wikipedia.HomotopyGroupsOfSpheres.UnitaryBlockDiagonal
