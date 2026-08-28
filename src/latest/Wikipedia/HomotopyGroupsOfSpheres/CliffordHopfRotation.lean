import Wikipedia.HomotopyGroupsOfSpheres.CliffordFourLatitude
import Wikipedia.HomotopyGroupsOfSpheres.SymmetricUnitaryReindex

/-! # The explicit complex rotation conjugating the Clifford pole to each latitude -/

noncomputable section

open scoped Matrix

namespace Wikipedia.HomotopyGroupsOfSpheres.CliffordFiveHermitian

def hopfRotation (q : EquatorSphere) (θ : ℝ) : unitary (Matrix (Fin 4) (Fin 4) ℂ) :=
  ⟨Matrix.reindex hopfBlockIndex hopfBlockIndex
    (ComplexUnitaryRotation.matrix (offDiagonalUnitary q) (θ / 2)),
    QuaternionicSymmetricMatrices.reindex_unitary hopfBlockIndex
      (ComplexUnitaryRotation.unitaryMap (offDiagonalUnitary q) (θ / 2))⟩

theorem hopfRotation_reindex (q : EquatorSphere) (θ : ℝ) :
    Matrix.reindex hopfBlockIndex.symm hopfBlockIndex.symm (hopfRotation q θ).val =
      ComplexUnitaryRotation.matrix (offDiagonalUnitary q) (θ / 2) :=
  (Matrix.reindex hopfBlockIndex hopfBlockIndex).symm_apply_apply _

theorem hopfRotation_zero (q : EquatorSphere) : hopfRotation q 0 = 1 := by
  apply Subtype.ext
  change Matrix.reindex hopfBlockIndex hopfBlockIndex
    (ComplexUnitaryRotation.matrix (offDiagonalUnitary q) (0 / 2)) = 1
  rw [zero_div, ComplexUnitaryRotation.matrix_zero]
  exact (Matrix.reindexRingEquiv ℂ hopfBlockIndex).map_one

theorem continuous_hopfRotation :
    Continuous (fun p : EquatorSphere × ℝ ↦ hopfRotation p.1 p.2) := by
  apply Continuous.subtype_mk
  exact (ComplexUnitaryRotation.continuous_matrix.comp
    ((continuous_offDiagonalUnitary.comp continuous_fst).prodMk
      (continuous_snd.div_const 2))).matrix_reindex hopfBlockIndex hopfBlockIndex

theorem matrix_pole_reindex :
    Matrix.reindex hopfBlockIndex.symm hopfBlockIndex.symm (matrix pole.val) =
      ComplexUnitaryRotation.grading := by
  have h := matrix_fourLatitudePoint 0 equatorPole
  rw [fourLatitudePoint_zero, ComplexUnitaryRotation.latitudeMatrix_zero] at h
  exact h

theorem hopfRotation_conjugate_pole (q : EquatorSphere) (θ : ℝ) :
    (hopfRotation q θ).val * matrix pole.val * (hopfRotation q θ).valᴴ =
      matrix (fourLatitudePoint θ q).val := by
  apply (Matrix.reindexRingEquiv ℂ hopfBlockIndex.symm).injective
  rw [map_mul, map_mul]
  change Matrix.reindex hopfBlockIndex.symm hopfBlockIndex.symm (hopfRotation q θ).val *
    Matrix.reindex hopfBlockIndex.symm hopfBlockIndex.symm (matrix pole.val) *
    Matrix.reindex hopfBlockIndex.symm hopfBlockIndex.symm (hopfRotation q θ).valᴴ =
      Matrix.reindex hopfBlockIndex.symm hopfBlockIndex.symm (matrix (fourLatitudePoint θ q).val)
  rw [← Matrix.conjTranspose_reindex, hopfRotation_reindex, matrix_pole_reindex,
    matrix_fourLatitudePoint]
  exact ComplexUnitaryRotation.matrix_half_conjugate_grading (offDiagonalUnitary q) θ

def correctedHopfRotation (q : EquatorSphere) (θ : ℝ) :
    unitary (Matrix (Fin 4) (Fin 4) ℂ) :=
  (hopfRotation equatorPole θ)⁻¹ * hopfRotation q θ

theorem correctedHopfRotation_zero (q : EquatorSphere) : correctedHopfRotation q 0 = 1 := by
  simp [correctedHopfRotation, hopfRotation_zero]

theorem correctedHopfRotation_reference (θ : ℝ) : correctedHopfRotation equatorPole θ = 1 :=
  inv_mul_cancel _

theorem continuous_correctedHopfRotation :
    Continuous (fun p : EquatorSphere × ℝ ↦ correctedHopfRotation p.1 p.2) :=
  (continuous_hopfRotation.comp (continuous_const.prodMk continuous_snd)).inv.mul
    continuous_hopfRotation

theorem correctedHopfRotation_pi (q : EquatorSphere) :
    Matrix.reindex hopfBlockIndex.symm hopfBlockIndex.symm (correctedHopfRotation q Real.pi).val =
      Matrix.fromBlocks (boundaryUnitary q).val 0 0
        ((offDiagonalUnitary equatorPole).valᴴ * (offDiagonalUnitary q).val) := by
  change (Matrix.reindexRingEquiv ℂ hopfBlockIndex.symm)
    ((hopfRotation equatorPole Real.pi).valᴴ * (hopfRotation q Real.pi).val) = _
  rw [map_mul]
  change Matrix.reindex hopfBlockIndex.symm hopfBlockIndex.symm
    (hopfRotation equatorPole Real.pi).valᴴ *
      Matrix.reindex hopfBlockIndex.symm hopfBlockIndex.symm (hopfRotation q Real.pi).val = _
  rw [← Matrix.conjTranspose_reindex, hopfRotation_reindex, hopfRotation_reindex]
  exact ComplexUnitaryRotation.reference_endpoint (offDiagonalUnitary equatorPole)
    (offDiagonalUnitary q)

end Wikipedia.HomotopyGroupsOfSpheres.CliffordFiveHermitian
