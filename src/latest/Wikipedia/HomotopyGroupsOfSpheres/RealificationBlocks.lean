import Wikipedia.HomotopyGroupsOfSpheres.ComplexMatrixRealification
import Mathlib.Logic.Equiv.Sum

/-! # Exact direct-sum coordinates for realification -/

noncomputable section

open scoped Matrix

namespace Wikipedia.HomotopyGroupsOfSpheres.ComplexMatrixRealification

variable {M N : Type*}

theorem matrix_reindex (e : M ≃ N) (A : Matrix M M ℂ) :
    matrix (Matrix.reindex e e A) =
      Matrix.reindex (Equiv.sumCongr e e) (Equiv.sumCongr e e) (matrix A) := by
  apply Matrix.ext
  intro i j
  rcases i with i | i <;> rcases j with j | j <;> rfl

theorem matrix_blockSum (A : Matrix M M ℂ) (B : Matrix N N ℂ) :
    matrix (Matrix.fromBlocks A 0 0 B) =
      Matrix.reindex (Equiv.sumSumSumComm M M N N) (Equiv.sumSumSumComm M M N N)
        (Matrix.fromBlocks (matrix A) 0 0 (matrix B)) := by
  apply Matrix.ext
  intro i j
  rcases i with (i | i) | (i | i) <;> rcases j with (j | j) | (j | j)
  all_goals simp [matrix, Matrix.reindex_apply, Equiv.sumSumSumComm]

theorem matrix_complexification [Fintype N] [DecidableEq N] (A : Matrix N N ℝ) :
    matrix (RealUnitaryMatrices.complexification A) = Matrix.fromBlocks A 0 0 A := by
  apply Matrix.ext
  intro i j
  rcases i with i | i <;> rcases j with j | j
  all_goals simp [matrix, RealUnitaryMatrices.complexification]

theorem affine_blockSum [DecidableEq M] [DecidableEq N]
    (c s : ℂ) (A : Matrix M M ℂ) (B : Matrix N N ℂ) :
    Matrix.fromBlocks (c • 1 + s • A) 0 0 (c • 1 + s • B) =
      c • (1 : Matrix (M ⊕ N) (M ⊕ N) ℂ) + s • Matrix.fromBlocks A 0 0 B := by
  apply Matrix.ext
  intro i j
  rcases i with i | i <;> rcases j with j | j
  all_goals simp [Matrix.one_apply, Sum.inl_ne_inr, Sum.inr_ne_inl]

theorem matrix_smul (r : ℝ) (A : Matrix N N ℂ) :
    matrix ((r : ℂ) • A) = r • matrix A := by
  apply Matrix.ext
  intro i j
  rcases i with i | i <;> rcases j with j | j
  all_goals simp [matrix, Complex.mul_re, Complex.mul_im]

end Wikipedia.HomotopyGroupsOfSpheres.ComplexMatrixRealification
