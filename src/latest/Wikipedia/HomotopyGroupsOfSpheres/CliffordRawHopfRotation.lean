import Wikipedia.HomotopyGroupsOfSpheres.CliffordHopfRotation
import Wikipedia.HomotopyGroupsOfSpheres.ComplexUnitaryRealification

/-! # The explicit Hopf rotation in the actual padded real Clifford coordinates -/

noncomputable section

open scoped Matrix

namespace Wikipedia.HomotopyGroupsOfSpheres.CliffordFiveHermitian

def paddedHopfRotation (q : EquatorSphere) (θ : ℝ) : unitary (Matrix (Fin 6) (Fin 6) ℂ) :=
  MatrixBorder.unitaryBorder ((1 : unitary ℂ),
    MatrixBorder.unitaryBorder ((1 : unitary ℂ), hopfRotation q θ))

theorem paddedHopfRotation_val (q : EquatorSphere) (θ : ℝ) :
    (paddedHopfRotation q θ).val =
      MatrixBorder.border 1 (MatrixBorder.border 1 (hopfRotation q θ).val) := rfl

theorem paddedHopfRotation_zero (q : EquatorSphere) : paddedHopfRotation q 0 = 1 := by
  apply Subtype.ext
  rw [paddedHopfRotation_val, hopfRotation_zero]
  exact (congrArg (MatrixBorder.border (1 : ℂ)) MatrixBorder.border_one).trans
    MatrixBorder.border_one

theorem continuous_paddedHopfRotation :
    Continuous (fun p : EquatorSphere × ℝ ↦ paddedHopfRotation p.1 p.2) := by
  apply Continuous.subtype_mk
  exact (MatrixBorder.continuous_border (1 : ℂ)).comp
    ((MatrixBorder.continuous_border (1 : ℂ)).comp
      (continuous_subtype_val.comp continuous_hopfRotation))

theorem paddedHopfRotation_conjugate_pole (q : EquatorSphere) (θ : ℝ) :
    (paddedHopfRotation q θ).val * paddedMatrix pole.val * (paddedHopfRotation q θ).valᴴ =
      paddedMatrix (fourLatitudePoint θ q).val := by
  rw [paddedHopfRotation_val]
  change MatrixBorder.border (1 : ℂ) (MatrixBorder.border 1 (hopfRotation q θ).val) *
    paddedMatrix pole.val * star
      (MatrixBorder.border (1 : ℂ) (MatrixBorder.border 1 (hopfRotation q θ).val)) = _
  simp only [paddedMatrix, MatrixBorder.star_border, star_one,
    ← MatrixBorder.border_mul, one_mul, mul_one]
  change MatrixBorder.border (-1 : ℂ)
    (MatrixBorder.border 1
      ((hopfRotation q θ).val * matrix pole.val * (hopfRotation q θ).valᴴ)) = _
  rw [hopfRotation_conjugate_pole]

def rawHopfRotation (q : EquatorSphere) (θ : ℝ) :
    unitary (Matrix (Fin 6 ⊕ Fin 6) (Fin 6 ⊕ Fin 6) ℝ) :=
  ComplexMatrixRealification.unitaryMap (paddedHopfRotation q θ)

theorem rawHopfRotation_zero (q : EquatorSphere) : rawHopfRotation q 0 = 1 := by
  change ComplexMatrixRealification.unitaryMap (paddedHopfRotation q 0) = 1
  rw [paddedHopfRotation_zero, map_one]

theorem continuous_rawHopfRotation :
    Continuous (fun p : EquatorSphere × ℝ ↦ rawHopfRotation p.1 p.2) :=
  ComplexMatrixRealification.continuous_unitaryMap.comp continuous_paddedHopfRotation

theorem rawHopfRotation_conjugate_pole (q : EquatorSphere) (θ : ℝ) :
    BalancedRealInvolutions.conjugate (rawHopfRotation q θ) (rawBalanced pole) =
      rawBalanced (fourLatitudePoint θ q) := by
  apply Subtype.ext
  change (ComplexMatrixRealification.unitaryMap (paddedHopfRotation q θ)).val *
    ComplexMatrixRealification.matrix (paddedMatrix pole.val) *
    (ComplexMatrixRealification.unitaryMap (paddedHopfRotation q θ)).val.transpose =
      ComplexMatrixRealification.matrix (paddedMatrix (fourLatitudePoint θ q).val)
  rw [← ComplexMatrixRealification.matrix_conjugate, paddedHopfRotation_conjugate_pole]

def correctedRawHopfRotation (q : EquatorSphere) (θ : ℝ) :
    unitary (Matrix (Fin 6 ⊕ Fin 6) (Fin 6 ⊕ Fin 6) ℝ) :=
  (rawHopfRotation equatorPole θ)⁻¹ * rawHopfRotation q θ

theorem correctedRawHopfRotation_zero (q : EquatorSphere) : correctedRawHopfRotation q 0 = 1 := by
  simp [correctedRawHopfRotation, rawHopfRotation_zero]

theorem correctedRawHopfRotation_reference (θ : ℝ) :
    correctedRawHopfRotation equatorPole θ = 1 := inv_mul_cancel _

theorem continuous_correctedRawHopfRotation :
    Continuous (fun p : EquatorSphere × ℝ ↦ correctedRawHopfRotation p.1 p.2) :=
  (continuous_rawHopfRotation.comp (continuous_const.prodMk continuous_snd)).inv.mul
    continuous_rawHopfRotation

end Wikipedia.HomotopyGroupsOfSpheres.CliffordFiveHermitian
