import Wikipedia.HomotopyGroupsOfSpheres.ComplexCliffordFive
import Wikipedia.HomotopyGroupsOfSpheres.SymmetricUnitaryReindex

/-! # The actual zero-corner reduction of the four-by-four Clifford family -/

noncomputable section

open scoped Matrix unitInterval

namespace Wikipedia.HomotopyGroupsOfSpheres.ComplexCliffordFive

open ComplexCrossProductUnitary

def rowSwapMatrix : Matrix (Fin 4) (Fin 4) ℂ :=
  !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 0, -1; 0, 0, 1, 0]

theorem rowSwapMatrix_unitary : rowSwapMatrix ∈ unitary (Matrix (Fin 4) (Fin 4) ℂ) := by
  have h : rowSwapMatrix * star rowSwapMatrix = 1 := by
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      norm_num [rowSwapMatrix, Matrix.mul_apply, Matrix.star_apply, Fin.sum_univ_succ,
        Matrix.cons_val_two, Matrix.cons_val_three]
  exact ⟨mul_eq_one_comm.mp h, h⟩

def rowSwap : unitary (Matrix (Fin 4) (Fin 4) ℂ) :=
  ⟨rowSwapMatrix, rowSwapMatrix_unitary⟩

def blockIndex : Fin 3 ⊕ Fin 1 ≃ Fin 4 := finSumFinEquiv

def swappedMap : C(UnitSphere, unitary (Matrix (Fin 3 ⊕ Fin 1) (Fin 3 ⊕ Fin 1) ℂ)) where
  toFun z := ⟨Matrix.reindex blockIndex.symm blockIndex.symm (rowSwap * unitaryMap z).val,
    QuaternionicSymmetricMatrices.reindex_unitary blockIndex.symm (rowSwap * unitaryMap z)⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (continuous_subtype_val.comp
      (continuous_const.mul unitaryMap.continuous)).matrix_reindex _ _

theorem swappedMap_corner (z : UnitSphere) : (swappedMap z).val.toBlocks₂₂ = 0 := by
  apply Matrix.ext
  intro i j
  fin_cases i
  fin_cases j
  change (rowSwapMatrix * matrix z.val) 3 3 = 0
  simp [rowSwapMatrix, matrix, Matrix.mul_apply, Fin.sum_univ_succ,
    Matrix.cons_val_three]

def cornerMap : C(UnitSphere, UnitaryZeroCorner.Domain (Fin 3) (Fin 1)) :=
  ⟨fun z ↦ ⟨swappedMap z, swappedMap_corner z⟩, swappedMap.continuous.subtype_mk _⟩

def reduced : C(UnitSphere, unitary (Matrix (Fin 3) (Fin 3) ℂ)) :=
  UnitaryZeroCorner.reduction.comp cornerMap

def reducedPolynomial (z : Vector) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![z 0 + star (z 2) * z 1, -star (z 2) ^ 2, -star (z 1) + star (z 2) * star (z 0);
     z 1 ^ 2, z 0 - z 1 * star (z 2), z 2 + z 1 * star (z 0);
     -z 2 + star (z 0) * z 1, -star (z 1) - star (z 0) * star (z 2), star (z 0) ^ 2]

theorem reduced_val (z : UnitSphere) : (reduced z).val = reducedPolynomial z.val := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [reduced, UnitaryZeroCorner.reduction, UnitaryZeroCorner.reducedMatrix,
      cornerMap, swappedMap, Matrix.reindex_apply, blockIndex, finSumFinEquiv,
      Matrix.toBlocks₁₁, Matrix.toBlocks₁₂, Matrix.toBlocks₂₁,
      Matrix.submatrix, rowSwap, rowSwapMatrix, unitaryMap, matrix, reducedPolynomial,
      Matrix.mul_apply, Matrix.cons_val_two] <;> ring

def rankReductionHomotopy : swappedMap.Homotopy
    (UnitaryZeroCorner.reducedInclusion.comp cornerMap) :=
  UnitaryZeroCorner.homotopy.compContinuousMap cornerMap

end Wikipedia.HomotopyGroupsOfSpheres.ComplexCliffordFive
