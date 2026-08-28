import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicReducedDenominator
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSchurComplexZero

/-!
# Exact preimage constraints at the midpoint of the Bott parameters

At `s=t=π/2`, a complex-valued projected column forces the middle row and
column of the symmetric matrix to decouple. These are midpoint statements;
they do not assert that every preimage occurs at the midpoint.
-/

noncomputable section

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicBottMatrix

open QuaternionicSymmetricMatrices QuaternionicComplexPlane QuaternionicScalars

local notation "ℍ" => Quaternion ℝ

theorem symmetric_entry (B : Space (Fin 3)) (r q : Fin 3) :
    B.val.val r q = B.val.val q r :=
  congrArg (fun A : Matrix (Fin 3) (Fin 3) ℂ ↦ A q r) B.property

theorem midpoint_matrix (B : Space (Fin 3)) :
    matrix (Real.cos (Real.pi / 2))
      (Real.sin (Real.pi / 2) * Real.cos (Real.pi / 2))
      (Real.sin (Real.pi / 2) * Real.sin (Real.pi / 2)) B = quaternionMatrix B.val.val := by
  simp only [matrix, skewPart, Real.cos_pi_div_two, Real.sin_pi_div_two,
    mul_zero, mul_one, zero_smul, one_smul, zero_add]

theorem midpoint_reference : scalarRotation (Real.pi / 2) (Real.pi / 2) = j := by
  simp only [scalarRotation, Real.cos_pi_div_two, Real.sin_pi_div_two,
    mul_zero, mul_one, zero_smul, one_smul, zero_add]

theorem midpoint_schur (B : Space (Fin 3)) (r : Fin 2) :
    firstColumnFormula (Real.pi / 2) (Real.pi / 2) B r =
      embed (B.val.val (remainingRow r) 1) - embed (B.val.val (remainingRow r) 0) *
        ((1 + Complex.normSq (B.val.val 1 0))⁻¹ • (1 - embed (B.val.val 1 0))) *
          embed (B.val.val 1 1) := by
  dsimp only [firstColumnFormula]
  simp only [midpoint_matrix, midpoint_reference, j_mul_j, neg_neg, star_one, mul_one]
  change embed (B.val.val (remainingRow r) 1) - embed (B.val.val (remainingRow r) 0) *
    (1 + embed (B.val.val 1 0))⁻¹ * embed (B.val.val 1 1) = _
  have hz : (embed (B.val.val 1 0)).re = 0 := by rw [embed_eq_mk]
  rw [inverse_one_add_of_re_zero _ hz, normSq_embed]

theorem midpoint_complexPart (B : Space (Fin 3)) (r : Fin 2) :
    complexPart (firstColumnFormula (Real.pi / 2) (Real.pi / 2) B r) =
      (1 + Complex.normSq (B.val.val 1 0))⁻¹ •
        (B.val.val (remainingRow r) 0 * star (B.val.val 1 1)) := by
  rw [midpoint_schur, complexPart_schur]

theorem midpoint_coordinate (B : Space (Fin 3)) (r : Fin 2) :
    coordinate (firstColumnFormula (Real.pi / 2) (Real.pi / 2) B r) =
      B.val.val (remainingRow r) 1 - (1 + Complex.normSq (B.val.val 1 0))⁻¹ •
        (B.val.val (remainingRow r) 0 * star (B.val.val 1 0) * B.val.val 1 1) := by
  rw [midpoint_schur, coordinate_schur]

theorem midpoint_of_zero_entry (B : Space (Fin 3)) (h10 : B.val.val 1 0 = 0) (r : Fin 2) :
    firstColumnFormula (Real.pi / 2) (Real.pi / 2) B r =
      ((B.val.val (remainingRow r) 0 * star (B.val.val 1 1) : ℂ) : ℍ) +
        embed (B.val.val (remainingRow r) 1) := by
  rw [midpoint_schur, schur_split, h10]
  simp only [Complex.normSq_zero, add_zero, inv_one, one_smul,
    star_zero, mul_zero, zero_mul, sub_zero]

theorem midpoint_coordinate_zero_iff (B : Space (Fin 3)) :
    coordinate (firstColumnFormula (Real.pi / 2) (Real.pi / 2) B 0) = 0 ↔
      B.val.val 1 0 = 0 := by
  rw [midpoint_coordinate]
  change B.val.val 0 1 - (1 + Complex.normSq (B.val.val 1 0))⁻¹ •
    (B.val.val 0 0 * star (B.val.val 1 0) * B.val.val 1 1) = 0 ↔ _
  rw [symmetric_entry B 0 1]
  exact schur_component_eq_zero_iff _ _ _
    (ComplexUnitaryEntryNorm.norm_entry_le_one B.val 0 0)
    (ComplexUnitaryEntryNorm.norm_entry_le_one B.val 1 1)

theorem midpoint_coordinate_one (B : Space (Fin 3)) (h10 : B.val.val 1 0 = 0) :
    coordinate (firstColumnFormula (Real.pi / 2) (Real.pi / 2) B 1) = B.val.val 2 1 := by
  rw [midpoint_coordinate]
  change B.val.val 2 1 - (1 + Complex.normSq (B.val.val 1 0))⁻¹ •
    (B.val.val 2 0 * star (B.val.val 1 0) * B.val.val 1 1) = _
  simp only [h10, star_zero, mul_zero, zero_mul, smul_zero, sub_zero]

theorem midpoint_middle_entry_unitary (B : Space (Fin 3))
    (h0 : coordinate (firstColumnFormula (Real.pi / 2) (Real.pi / 2) B 0) = 0)
    (h1 : coordinate (firstColumnFormula (Real.pi / 2) (Real.pi / 2) B 1) = 0) :
    B.val.val 1 1 ∈ unitary ℂ := by
  have h10 := (midpoint_coordinate_zero_iff B).mp h0
  have h01 : B.val.val 0 1 = 0 := (symmetric_entry B 0 1).trans h10
  have h21 : B.val.val 2 1 = 0 := (midpoint_coordinate_one B h10).symm.trans h1
  have hs := ComplexUnitaryEntryNorm.sum_normSq_column B.val 1
  rw [Fin.sum_univ_three, h01, h21, Complex.normSq_zero, zero_add, add_zero] at hs
  constructor
  · rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, hs, Complex.ofReal_one]
  · rw [Complex.star_def, Complex.mul_conj, hs, Complex.ofReal_one]

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicBottMatrix
