import Wikipedia.HomotopyGroupsOfSpheres.MatrixBorder
import Wikipedia.HomotopyGroupsOfSpheres.SymmetricUnitaryDeterminant

/-! # The actual identity-block inclusions of symmetric unitary parameter spaces -/

noncomputable section

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSymmetricMatrices

open MatrixBorder

def stabilization (n : ℕ) : C(Space (Fin n), Space (Fin (n + 1))) where
  toFun B := ⟨unitaryBorder (1, B.val), by
    change (border 1 B.val.val).transpose = border 1 B.val.val
    rw [transpose_border, B.property]⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact (continuous_border (1 : ℂ)).comp
      (continuous_subtype_val.comp continuous_subtype_val)

theorem stabilization_val (n : ℕ) (B : Space (Fin n)) :
    (stabilization n B).val.val = border 1 B.val.val := rfl

theorem stabilization_identity (n : ℕ) : stabilization n identity = identity := by
  apply Subtype.ext
  apply Subtype.ext
  exact border_one

theorem stabilization_determinant (n : ℕ) (B : Space (Fin n)) :
    determinant (stabilization n B) = determinant B := by
  apply Circle.ext
  change (border (1 : ℂ) B.val.val).det = B.val.val.det
  rw [det_border, one_mul]

def specialStabilization (n : ℕ) : C(SpecialSpace (Fin n), SpecialSpace (Fin (n + 1))) where
  toFun B := ⟨stabilization n B.val, by
    rw [show (stabilization n B.val) ∈ specialLocus (Fin (n + 1)) ↔
      determinant (stabilization n B.val) = 1 from Iff.rfl, stabilization_determinant]
    exact B.property⟩
  continuous_toFun := ((stabilization n).continuous.comp continuous_subtype_val).subtype_mk _

theorem specialStabilization_identity (n : ℕ) :
    specialStabilization n specialIdentity = specialIdentity := by
  apply Subtype.ext
  exact stabilization_identity n

def stabilizationIterate (n : ℕ) : (r : ℕ) → C(Space (Fin n), Space (Fin (n + r)))
  | 0 => ContinuousMap.id _
  | r + 1 => (stabilization (n + r)).comp (stabilizationIterate n r)

theorem stabilizationIterate_identity (n r : ℕ) :
    stabilizationIterate n r identity = identity := by
  induction r with
  | zero => rfl
  | succ r ih =>
    change stabilization (n + r) (stabilizationIterate n r identity) = identity
    rw [ih, stabilization_identity]

theorem stabilizationIterate_determinant (n r : ℕ) (B : Space (Fin n)) :
    determinant (stabilizationIterate n r B) = determinant B := by
  induction r with
  | zero => rfl
  | succ r ih =>
    change determinant (stabilization (n + r) (stabilizationIterate n r B)) = determinant B
    rw [stabilization_determinant, ih]

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSymmetricMatrices
