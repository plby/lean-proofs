import Wikipedia.HomotopyGroupsOfSpheres.SymmetricUnitaryDeterminant

/-! # Unitary congruence on the actual symmetric unitary and determinant-one loci -/

noncomputable section

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSymmetricMatrices

variable {N : Type*} [Fintype N] [DecidableEq N]

def congruence (U : unitary (Matrix N N ℂ)) (B : Space N) : Space N :=
  ⟨U * B.val * Matrix.UnitaryGroup.transpose U, by
    change (U.val * B.val.val * U.val.transpose).transpose =
      U.val * B.val.val * U.val.transpose
    rw [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_mul, B.property]
    exact (mul_assoc _ _ _).symm⟩

@[simp] theorem congruence_one (B : Space N) : congruence 1 B = B := by
  apply Subtype.ext
  apply Subtype.ext
  change (1 : Matrix N N ℂ) * B.val.val * (1 : Matrix N N ℂ).transpose = B.val.val
  rw [Matrix.transpose_one, one_mul, mul_one]

theorem congruence_mul (U V : unitary (Matrix N N ℂ)) (B : Space N) :
    congruence U (congruence V B) = congruence (U * V) B := by
  apply Subtype.ext
  apply Subtype.ext
  change U.val * (V.val * B.val.val * V.val.transpose) * U.val.transpose =
    (U.val * V.val) * B.val.val * (U.val * V.val).transpose
  simp only [Matrix.transpose_mul, mul_assoc]

theorem congruence_inv_cancel (U : unitary (Matrix N N ℂ)) (B : Space N) :
    congruence U⁻¹ (congruence U B) = B := by
  rw [congruence_mul, inv_mul_cancel, congruence_one]

theorem congruence_det (U : unitary (Matrix N N ℂ)) (B : Space N) :
    (congruence U B).val.val.det = U.val.det ^ 2 * B.val.val.det := by
  change (U.val * B.val.val * U.val.transpose).det = _
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  ring

theorem continuous_congruence :
    Continuous (fun z : unitary (Matrix N N ℂ) × Space N ↦ congruence z.1 z.2) := by
  have hU : Continuous (fun z : unitary (Matrix N N ℂ) × Space N ↦ z.1.val) :=
    continuous_subtype_val.comp continuous_fst
  have hB : Continuous (fun z : unitary (Matrix N N ℂ) × Space N ↦ z.2.val.val) :=
    continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd)
  exact (((hU.mul hB).mul hU.matrix_transpose).subtype_mk _).subtype_mk _

def congruenceSpecial (U : unitary (Matrix N N ℂ)) (hU : U.val.det ^ 2 = 1)
    (B : SpecialSpace N) : SpecialSpace N :=
  ⟨congruence U B.val, by
    apply Circle.ext
    change (congruence U B.val).val.val.det = 1
    rw [congruence_det, hU, one_mul]
    exact congrArg (fun z : Circle ↦ (z : ℂ)) B.property⟩

theorem continuous_congruenceSpecial {X : Type*} [TopologicalSpace X]
    (U : X → unitary (Matrix N N ℂ)) (hU : ∀ x, (U x).val.det ^ 2 = 1)
    (B : X → SpecialSpace N) (hcU : Continuous U) (hcB : Continuous B) :
    Continuous (fun x ↦ congruenceSpecial (U x) (hU x) (B x)) :=
  (continuous_congruence.comp
    (hcU.prodMk (continuous_subtype_val.comp hcB))).subtype_mk _

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSymmetricMatrices
