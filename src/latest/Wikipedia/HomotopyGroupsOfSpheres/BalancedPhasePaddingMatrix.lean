import Wikipedia.HomotopyGroupsOfSpheres.BalancedPhasePadding
import Wikipedia.HomotopyGroupsOfSpheres.RealificationBlocks
import Wikipedia.HomotopyGroupsOfSpheres.MatrixBorder
import Wikipedia.HomotopyGroupsOfSpheres.BalancedRotationPaths

/-! # The phase-padding endpoint is the exact balanced rotation matrix -/

noncomputable section

open scoped Matrix

namespace Wikipedia.HomotopyGroupsOfSpheres.BalancedPhasePadding

open QuaternionicSymmetricMatrices RealUnitaryMatrices ComplexMatrixRealification

def pairMatrix : Matrix (Fin 2) (Fin 2) ℝ := !![-1, 0; 0, 1]

theorem pairMatrix_complexification : complexification pairMatrix = !![-1, 0; 0, 1] := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [pairMatrix, complexification]

theorem phasePair_rotation (θ : ℝ) :
    (phasePair θ).val.val = (Real.cos θ : ℂ) • 1 +
      ((Real.sin θ : ℂ) * Complex.I) • complexification pairMatrix := by
  rw [phasePair_val, pairMatrix_complexification]
  simp only [Circle.coe_exp, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
    Complex.ofReal_neg]
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num

theorem pair_border (H : Matrix (Fin 4) (Fin 4) ℂ) :
    Matrix.reindex finSumFinEquiv finSumFinEquiv
      (Matrix.fromBlocks (!![-1, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℂ) 0 0 H) =
        MatrixBorder.border (-1) (MatrixBorder.border 1 H) := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> rfl

theorem realification_padding (H : Matrix (Fin 4) (Fin 4) ℂ) :
    matrix (MatrixBorder.border (-1) (MatrixBorder.border 1 H)) =
      Matrix.reindex paddingIndex paddingIndex
        (Matrix.fromBlocks (Matrix.fromBlocks pairMatrix 0 0 pairMatrix) 0 0 (matrix H)) := by
  rw [← pair_border, matrix_reindex, matrix_blockSum,
    ← pairMatrix_complexification, matrix_complexification]
  rfl

theorem complexification_blockSum {M N : Type} [Fintype M] [DecidableEq M]
    [Fintype N] [DecidableEq N] (A : Matrix M M ℝ) (B : Matrix N N ℝ) :
    complexification (Matrix.fromBlocks A 0 0 B) =
      Matrix.fromBlocks (complexification A) 0 0 (complexification B) := by
  apply Matrix.ext
  intro i j
  rcases i with i | i <;> rcases j with j | j
  all_goals simp [complexification]

theorem complexification_reindex {M N : Type} [Fintype M] [DecidableEq M]
    [Fintype N] [DecidableEq N] (e : M ≃ N) (A : Matrix M M ℝ) :
    complexification (Matrix.reindex e e A) =
      Matrix.reindex e e (complexification A) := rfl

theorem affine_reindex {M N : Type} [DecidableEq M]
    [DecidableEq N] (e : M ≃ N) (c s : ℂ) (A : Matrix M M ℂ) :
    Matrix.reindex e e (c • 1 + s • A) = c • 1 + s • Matrix.reindex e e A := by
  have h1 : Matrix.reindexLinearEquiv ℂ ℂ e e (1 : Matrix M M ℂ) = 1 :=
    Matrix.submatrix_one_equiv e.symm
  change Matrix.reindexLinearEquiv ℂ ℂ e e (c • 1 + s • A) =
    c • 1 + s • Matrix.reindexLinearEquiv ℂ ℂ e e A
  rw [map_add, map_smul, map_smul, h1]

theorem padding_rotation_val (θ : ℝ) (H : Matrix (Fin 4) (Fin 4) ℂ)
    (B : Space (Fin 4 ⊕ Fin 4))
    (hB : B.val.val = BalancedRealInvolutions.rotationMatrix 4 θ (matrix H)) :
    (padding (θ, B)).val.val = BalancedRealInvolutions.rotationMatrix 6 θ
      (matrix (MatrixBorder.border (-1) (MatrixBorder.border 1 H))) := by
  change Matrix.reindex paddingIndex paddingIndex
    (Matrix.fromBlocks (Matrix.fromBlocks (phasePair θ).val.val 0 0
      (phasePair θ).val.val) 0 0 B.val.val) = _
  rw [phasePair_rotation, hB, BalancedRealInvolutions.rotationMatrix,
    affine_blockSum, affine_blockSum, ← complexification_blockSum,
    ← complexification_blockSum, affine_reindex, ← complexification_reindex]
  rw [← realification_padding]
  rfl

end Wikipedia.HomotopyGroupsOfSpheres.BalancedPhasePadding
