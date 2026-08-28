import Wikipedia.HomotopyGroupsOfSpheres.CliffordRawHopfRotation
import Wikipedia.HomotopyGroupsOfSpheres.CliffordCanonicalPoleFrame
import Wikipedia.HomotopyGroupsOfSpheres.BalancedFrameAction

/-! # The explicit orthogonal endpoint matrix in the positive Clifford coordinates -/

noncomputable section

open scoped Matrix

namespace Wikipedia.HomotopyGroupsOfSpheres.CliffordFiveHermitian

open NoExoticSixSphere.GLOrthonormalization BalancedRealInvolutions

def boundaryPaddedUnitary (q : EquatorSphere) : unitary (Matrix (Fin 3) (Fin 3) ℂ) :=
  MatrixBorder.unitaryBorder ((1 : unitary ℂ), boundaryUnitary q)

theorem boundaryPaddedUnitary_val (q : EquatorSphere) :
    (boundaryPaddedUnitary q).val = MatrixBorder.border 1 (boundaryUnitary q).val := rfl

theorem boundaryPaddedUnitary_equatorPole : boundaryPaddedUnitary equatorPole = 1 := by
  apply Subtype.ext
  rw [boundaryPaddedUnitary_val, boundaryUnitary_equatorPole]
  exact MatrixBorder.border_one

theorem continuous_boundaryPaddedUnitary : Continuous boundaryPaddedUnitary :=
  ((MatrixBorder.continuous_border (1 : ℂ)).comp
    (continuous_subtype_val.comp continuous_boundaryUnitary)).subtype_mk _

def boundaryOrthogonal (q : EquatorSphere) : OrthogonalOperators 6 :=
  matrixOrthogonal (n := 3) (ComplexMatrixRealification.unitaryMap (boundaryPaddedUnitary q))

theorem boundaryOrthogonal_equatorPole : boundaryOrthogonal equatorPole = 1 := by
  change matrixOrthogonal (ComplexMatrixRealification.unitaryMap
    (boundaryPaddedUnitary equatorPole)) = 1
  rw [boundaryPaddedUnitary_equatorPole, map_one, map_one]

theorem continuous_boundaryOrthogonal : Continuous boundaryOrthogonal :=
  continuous_matrixOrthogonal.comp
    (ComplexMatrixRealification.continuous_unitaryMap.comp continuous_boundaryPaddedUnitary)

theorem correctedRawHopfRotation_val (q : EquatorSphere) (θ : ℝ) :
    (correctedRawHopfRotation q θ).val =
      ComplexMatrixRealification.matrix
        (MatrixBorder.border 1 (MatrixBorder.border 1 (correctedHopfRotation q θ).val)) := by
  change ((ComplexMatrixRealification.unitaryMap (paddedHopfRotation equatorPole θ))⁻¹ *
    ComplexMatrixRealification.unitaryMap (paddedHopfRotation q θ)).val = _
  rw [← map_inv, ← map_mul]
  change ComplexMatrixRealification.matrix
    (star (paddedHopfRotation equatorPole θ).val * (paddedHopfRotation q θ).val) = _
  rw [paddedHopfRotation_val, paddedHopfRotation_val]
  simp only [MatrixBorder.star_border, star_one, ← MatrixBorder.border_mul, one_mul]
  rfl

theorem correctedHopfRotation_pi_positive (q : EquatorSphere) (i j : Fin 2) :
    (correctedHopfRotation q Real.pi).val (hopfBlockIndex (Sum.inl i))
      (hopfBlockIndex (Sum.inl j)) = (boundaryUnitary q).val i j :=
  congrArg (fun M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℂ ↦ M (Sum.inl i) (Sum.inl j))
    (correctedHopfRotation_pi q)

def positiveComplexIndex (i : Fin 3) : Fin 6 := ⟨i.val + 1, by omega⟩

theorem positiveComplexIndex_zero : positiveComplexIndex 0 = (0 : Fin 5).succ := rfl

theorem positiveComplexIndex_succ (i : Fin 2) :
    positiveComplexIndex i.succ = (hopfBlockIndex (Sum.inl i)).succ.succ := rfl

theorem corrected_padded_positive_block (q : EquatorSphere) :
    (MatrixBorder.border 1 (MatrixBorder.border 1 (correctedHopfRotation q Real.pi).val)).submatrix
      positiveComplexIndex positiveComplexIndex = (boundaryPaddedUnitary q).val := by
  apply Matrix.ext
  intro i j
  cases i using Fin.cases <;> cases j using Fin.cases <;>
    simp [Matrix.submatrix_apply, positiveComplexIndex_zero, positiveComplexIndex_succ,
      boundaryPaddedUnitary_val, correctedHopfRotation_pi_positive] <;> rfl

theorem polePositiveIndex_sum (i : Fin 3 ⊕ Fin 3) :
    (finSumFinEquiv : Fin 6 ⊕ Fin 6 ≃ Fin 12).symm
      (polePositiveIndex ((finSumFinEquiv : Fin 3 ⊕ Fin 3 ≃ Fin 6) i)) =
        Sum.map positiveComplexIndex positiveComplexIndex i := by
  rcases i with i | i <;> fin_cases i <;> rfl

theorem correctedRawHopfRotation_positive_coordinates (q : EquatorSphere) (i j : Fin 6) :
    (correctedRawHopfRotation q Real.pi).val
      ((finSumFinEquiv : Fin 6 ⊕ Fin 6 ≃ Fin 12).symm (polePositiveIndex i))
      (finSumFinEquiv.symm (polePositiveIndex j)) =
        (ComplexMatrixRealification.unitaryMap (boundaryPaddedUnitary q)).val
          ((finSumFinEquiv : Fin 3 ⊕ Fin 3 ≃ Fin 6).symm i) (finSumFinEquiv.symm j) := by
  have hentry (a b : Fin 3) :
      MatrixBorder.border 1 (MatrixBorder.border 1 (correctedHopfRotation q Real.pi).val)
        (positiveComplexIndex a) (positiveComplexIndex b) = (boundaryPaddedUnitary q).val a b :=
    congrArg (fun M : Matrix (Fin 3) (Fin 3) ℂ ↦ M a b) (corrected_padded_positive_block q)
  obtain ⟨i, rfl⟩ := (finSumFinEquiv : Fin 3 ⊕ Fin 3 ≃ Fin 6).surjective i
  obtain ⟨j, rfl⟩ := (finSumFinEquiv : Fin 3 ⊕ Fin 3 ≃ Fin 6).surjective j
  rw [polePositiveIndex_sum, polePositiveIndex_sum, Equiv.symm_apply_apply,
    Equiv.symm_apply_apply, correctedRawHopfRotation_val, ComplexMatrixRealification.unitaryMap_val]
  rcases i with i | i <;> rcases j with j | j <;>
    simp [ComplexMatrixRealification.matrix, hentry]

end Wikipedia.HomotopyGroupsOfSpheres.CliffordFiveHermitian
