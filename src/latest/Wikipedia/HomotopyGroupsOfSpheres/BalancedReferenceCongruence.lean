import Wikipedia.HomotopyGroupsOfSpheres.BalancedRotationPaths

/-! # Congruence by the balanced diagonal reference path -/

noncomputable section

namespace Wikipedia.HomotopyGroupsOfSpheres.BalancedRealInvolutions

open QuaternionicSymmetricMatrices

theorem diagonalUnitary_zero (n : ℕ) : diagonalUnitary n 0 = 1 :=
  Subtype.ext (diagonalPhase_zero n)

theorem diagonalUnitary_add (n : ℕ) (θ φ : ℝ) :
    diagonalUnitary n θ * diagonalUnitary n φ = diagonalUnitary n (θ + φ) :=
  Subtype.ext (diagonalPhase_add n θ φ)

theorem diagonalSpecial_zero (n : ℕ) : diagonalSpecial n 0 = specialIdentity := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  exact diagonalPhase_zero n

def referenceAction (n : ℕ) (θ : ℝ) (B : SpecialSpace (Index n)) : SpecialSpace (Index n) :=
  congruenceSpecial (diagonalUnitary n θ) (by
    change (diagonalPhase n θ).det ^ 2 = 1
    rw [diagonalPhase_det, one_pow]) B

theorem continuous_referenceAction (n : ℕ) :
    Continuous (fun z : ℝ × SpecialSpace (Index n) ↦ referenceAction n z.1 z.2) := by
  have hU : Continuous (fun z : ℝ × SpecialSpace (Index n) ↦ diagonalPhase n z.1) :=
    (continuous_diagonalPhase n).comp continuous_fst
  have hB : Continuous (fun z : ℝ × SpecialSpace (Index n) ↦ z.2.val.val.val) :=
    continuous_subtype_val.comp
      (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd))
  have hc : Continuous (fun z : ℝ × SpecialSpace (Index n) ↦
      diagonalPhase n z.1 * z.2.val.val.val * (diagonalPhase n z.1).transpose) :=
    (hU.matrix_mul hB).matrix_mul hU.matrix_transpose
  exact ((hc.subtype_mk _).subtype_mk _).subtype_mk _

theorem referenceAction_zero (n : ℕ) (B : SpecialSpace (Index n)) : referenceAction n 0 B = B := by
  apply Subtype.ext
  change congruence (diagonalUnitary n 0) B.val = B.val
  rw [diagonalUnitary_zero, congruence_one]

theorem referenceAction_add (n : ℕ) (θ φ : ℝ) (B : SpecialSpace (Index n)) :
    referenceAction n θ (referenceAction n φ B) = referenceAction n (θ + φ) B := by
  apply Subtype.ext
  change congruence (diagonalUnitary n θ) (congruence (diagonalUnitary n φ) B.val) =
    congruence (diagonalUnitary n (θ + φ)) B.val
  rw [congruence_mul, diagonalUnitary_add]

theorem referenceAction_cancel (n : ℕ) (θ : ℝ) (B : SpecialSpace (Index n)) :
    referenceAction n (-θ) (referenceAction n θ B) = B := by
  rw [referenceAction_add, neg_add_cancel, referenceAction_zero]

theorem referenceAction_diagonal (n : ℕ) (θ φ : ℝ) :
    referenceAction n θ (diagonalSpecial n φ) = diagonalSpecial n (2 * θ + φ) := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  change diagonalPhase n θ * diagonalPhase n φ * (diagonalPhase n θ).transpose = _
  rw [show (diagonalPhase n θ).transpose = diagonalPhase n θ from Matrix.diagonal_transpose _,
    diagonalPhase_add, diagonalPhase_add]
  congr 1
  ring

theorem referenceAction_reference (n : ℕ) (θ : ℝ) :
    referenceAction n (-θ / 2) (rotation (standard n) θ) = specialIdentity := by
  rw [rotation_standard, referenceAction_diagonal,
    show 2 * (-θ / 2) + θ = 0 by ring, diagonalSpecial_zero]

end Wikipedia.HomotopyGroupsOfSpheres.BalancedRealInvolutions
