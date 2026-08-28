import Wikipedia.HomotopyGroupsOfSpheres.ComplexCliffordSymmetricReduction

/-! # The actual output coordinates matching the stabilized cross-product map -/

noncomputable section

open scoped Matrix

namespace Wikipedia.HomotopyGroupsOfSpheres.ComplexCliffordFive

open QuaternionicSymmetricMatrices

local notation "BlockIndex" => Fin 3 ⊕ Fin 1

def blockLeftMatrix : Matrix BlockIndex BlockIndex ℂ := Matrix.fromBlocks leftFactor 0 0 1

theorem blockLeftMatrix_real (i j : BlockIndex) :
    star (blockLeftMatrix i j) = blockLeftMatrix i j := by
  rcases i with i | i <;> rcases j with j | j
  all_goals fin_cases i <;> fin_cases j <;> norm_num [blockLeftMatrix, leftFactor]

theorem blockLeftMatrix_unitary : blockLeftMatrix ∈ unitary (Matrix BlockIndex BlockIndex ℂ) := by
  have ht : star blockLeftMatrix = blockLeftMatrix.transpose := by
    apply Matrix.ext
    intro i j
    exact blockLeftMatrix_real j i
  have hr : blockLeftMatrix * star blockLeftMatrix = 1 := by
    rw [ht, blockLeftMatrix, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply]
    simp only [Matrix.transpose_zero, Matrix.transpose_one, Matrix.mul_zero, Matrix.zero_mul,
      add_zero, zero_add, Matrix.one_mul, leftFactor_mul_transpose, Matrix.fromBlocks_one]
  exact ⟨mul_eq_one_comm.mp hr, hr⟩

def blockLeft : unitary (Matrix BlockIndex BlockIndex ℂ) :=
  ⟨blockLeftMatrix, blockLeftMatrix_unitary⟩

def frontIndex : BlockIndex ≃ Fin 4 :=
  (Equiv.sumComm (Fin 3) (Fin 1)).trans finSumFinEquiv

theorem frontIndex_reindex_block (B : Matrix (Fin 3) (Fin 3) ℂ) :
    Matrix.reindex frontIndex frontIndex (Matrix.fromBlocks B 0 0 1) =
      MatrixBorder.border 1 B := by
  apply Matrix.ext
  intro i j
  obtain ⟨i, rfl⟩ := frontIndex.surjective i
  obtain ⟨j, rfl⟩ := frontIndex.surjective j
  change Matrix.fromBlocks B 0 0 1 (frontIndex.symm (frontIndex i))
    (frontIndex.symm (frontIndex j)) = MatrixBorder.border 1 B (frontIndex i) (frontIndex j)
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  rcases i with i | i <;> rcases j with j | j
  all_goals fin_cases i <;> fin_cases j <;> rfl

def outputTransform : C(Space BlockIndex, Space (Fin 4)) where
  toFun B := reindex frontIndex (congruence blockLeft B)
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    change Continuous (fun B : Space BlockIndex ↦ Matrix.reindex frontIndex frontIndex
      (blockLeft.val * B.val.val * blockLeft.val.transpose))
    have hB : Continuous (fun B : Space BlockIndex ↦ B.val.val) :=
      continuous_subtype_val.comp continuous_subtype_val
    exact ((continuous_const.mul hB).mul continuous_const).matrix_reindex _ _

theorem outputTransform_identity : outputTransform identity = identity := by
  change reindex frontIndex (unitaryProjection blockLeft) = identity
  rw [unitaryProjection_eq_identity_of_real blockLeft blockLeftMatrix_real, reindex_identity]

theorem outputTransform_block (B : Space BlockIndex) (A : Matrix (Fin 3) (Fin 3) ℂ)
    (hB : B.val.val = Matrix.fromBlocks A 0 0 1) :
    (outputTransform B).val.val =
      MatrixBorder.border 1 (leftFactor * A * leftFactor.transpose) := by
  change Matrix.reindex frontIndex frontIndex
    (blockLeftMatrix * B.val.val * blockLeftMatrix.transpose) = _
  rw [hB, blockLeftMatrix, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_multiply]
  simp only [Matrix.transpose_zero, Matrix.transpose_one, Matrix.mul_zero, Matrix.zero_mul,
    add_zero, zero_add, Matrix.one_mul]
  exact frontIndex_reindex_block _

theorem outputTransform_reduced (z : ComplexCrossProductUnitary.UnitSphere) :
    outputTransform (blockSymmetricReduced (parameterHomeomorph z)) =
      stabilization 3 (ComplexCrossProductUnitary.symmetricMap z) := by
  apply Subtype.ext
  apply Subtype.ext
  rw [outputTransform_block _ _ (blockSymmetricReduced_val _), stabilization_val,
    reduced_symmetric_crossProduct]

end Wikipedia.HomotopyGroupsOfSpheres.ComplexCliffordFive
