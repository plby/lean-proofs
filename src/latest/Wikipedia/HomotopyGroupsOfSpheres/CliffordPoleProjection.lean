import Wikipedia.HomotopyGroupsOfSpheres.CliffordSixBalanced
import Wikipedia.HomotopyGroupsOfSpheres.MatrixBorderDiagonal
import Wikipedia.HomotopyGroupsOfSpheres.ComplexRealDiagonal
import Wikipedia.HomotopyGroupsOfSpheres.BalancedPositiveProjection

/-! # The exact positive-coordinate projection at the raw Clifford pole -/

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator

namespace Wikipedia.HomotopyGroupsOfSpheres.CliffordFiveHermitian

open NoExoticSixSphere.GLOrthonormalization BalancedRealInvolutions

def polePositiveComplexMask : Fin 6 → ℝ := ![0, 1, 1, 1, 0, 0]

def polePositiveMask (i : Fin 12) : ℝ :=
  Sum.elim polePositiveComplexMask polePositiveComplexMask
    ((finSumFinEquiv : Fin 6 ⊕ Fin 6 ≃ Fin 12).symm i)

theorem polePositiveMask_eq (i : Fin 12) :
    polePositiveMask i = if i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 7 ∨ i = 8 ∨ i = 9 then 1 else 0 := by
  fin_cases i <;> rfl

theorem matrix_pole_diagonal :
    matrix pole.val = Matrix.diagonal ![(1 : ℂ), 1, -1, -1] := by
  change matrix (fun i ↦ pole.val i) = _
  rw [pole_val]
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    norm_num [matrix, Matrix.diagonal_apply, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four]

theorem paddedMatrix_pole_diagonal :
    paddedMatrix pole.val =
      Matrix.diagonal (fun i ↦ ((2 * polePositiveComplexMask i - 1 : ℝ) : ℂ)) := by
  rw [paddedMatrix, matrix_pole_diagonal, MatrixBorder.border_diagonal,
    MatrixBorder.border_diagonal]
  apply congrArg Matrix.diagonal
  change (![-1, 1, 1, 1, -1, -1] : Fin 6 → ℂ) = _
  have hC : (![-1, 1, 1, 1, -1, -1] : Fin 6 → ℂ) 5 = -1 := rfl
  have hR : (![0, 1, 1, 1, 0, 0] : Fin 6 → ℝ) 5 = 0 := rfl
  funext i
  fin_cases i <;>
    norm_num [polePositiveComplexMask, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, hC, hR]

theorem positiveMatrix_raw_pole :
    positiveMatrix (rawBalanced pole) =
      Matrix.diagonal (Sum.elim polePositiveComplexMask polePositiveComplexMask) := by
  have hA : ComplexMatrixRealification.matrix (paddedMatrix pole.val) =
      Matrix.diagonal (fun i : Fin 6 ⊕ Fin 6 ↦
        2 * Sum.elim polePositiveComplexMask polePositiveComplexMask i - 1) := by
    rw [paddedMatrix_pole_diagonal, ComplexMatrixRealification.matrix_ofReal_diagonal]
    congr 1
    funext i
    cases i <;> rfl
  rw [positiveMatrix, rawBalanced_val, hA]
  apply Matrix.ext
  intro i j
  by_cases h : i = j
  · subst j
    norm_num [Matrix.diagonal_apply, Matrix.one_apply]
    ring
  · simp [h]

theorem positiveProjection_raw_pole_apply (x : Vector 12) (i : Fin 12) :
    positiveProjection (rawBalanced pole) x i = polePositiveMask i * x i := by
  change (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin 12)
    (Matrix.reindex finSumFinEquiv finSumFinEquiv (positiveMatrix (rawBalanced pole))) x).ofLp i = _
  rw [positiveMatrix_raw_pole, Matrix.ofLp_toEuclideanCLM]
  change ((Matrix.diagonal (Sum.elim polePositiveComplexMask polePositiveComplexMask)).submatrix
    (finSumFinEquiv : Fin 6 ⊕ Fin 6 ≃ Fin 12).symm finSumFinEquiv.symm *ᵥ x.ofLp) i = _
  rw [Matrix.submatrix_diagonal_equiv, Matrix.mulVec_diagonal]
  rfl

end Wikipedia.HomotopyGroupsOfSpheres.CliffordFiveHermitian
