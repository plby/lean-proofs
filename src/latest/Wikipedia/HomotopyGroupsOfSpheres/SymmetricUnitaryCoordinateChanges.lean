import Wikipedia.HomotopyGroupsOfSpheres.UnitaryDirectSum
import Wikipedia.HomotopyGroupsOfSpheres.SymmetricUnitaryProjection

/-! # Based coordinate homeomorphisms and exact direct-sum naturality -/

noncomputable section

open scoped Matrix

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSymmetricMatrices

variable {M N : Type} [Fintype M] [DecidableEq M] [Fintype N] [DecidableEq N]

theorem continuous_congruence_const (U : unitary (Matrix N N ℂ)) :
    Continuous (congruence U) := by
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  change Continuous (fun B : Space N ↦ U.val * B.val.val * U.val.transpose)
  have hB : Continuous (fun B : Space N ↦ B.val.val) :=
    continuous_subtype_val.comp continuous_subtype_val
  exact (continuous_const.mul hB).mul continuous_const

def congruenceSpaceHomeomorph (U : unitary (Matrix N N ℂ)) : Space N ≃ₜ Space N where
  toFun := congruence U
  invFun := congruence U⁻¹
  left_inv := congruence_inv_cancel U
  right_inv B := by simpa only [inv_inv] using congruence_inv_cancel U⁻¹ B
  continuous_toFun := continuous_congruence_const U
  continuous_invFun := continuous_congruence_const U⁻¹

theorem congruenceSpaceHomeomorph_identity (U : unitary (Matrix N N ℂ))
    (hU : ∀ i j, star (U.val i j) = U.val i j) :
    congruenceSpaceHomeomorph U identity = identity :=
  unitaryProjection_eq_identity_of_real U hU

theorem congruence_blockSum (U : unitary (Matrix M M ℂ)) (V : unitary (Matrix N N ℂ))
    (A : Space M) (B : Space N) :
    congruence (UnitaryDirectSum.inclusion (U, V)) (blockSum A B) =
      blockSum (congruence U A) (congruence V B) := by
  apply Subtype.ext
  apply Subtype.ext
  change Matrix.fromBlocks U.val 0 0 V.val * Matrix.fromBlocks A.val.val 0 0 B.val.val *
      (Matrix.fromBlocks U.val 0 0 V.val).transpose =
    Matrix.fromBlocks (U.val * A.val.val * U.val.transpose) 0 0
      (V.val * B.val.val * V.val.transpose)
  simp [Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply]

theorem reindex_blockSum {M' N' : Type} [Fintype M'] [DecidableEq M']
    [Fintype N'] [DecidableEq N'] (e : M ≃ M') (f : N ≃ N') (A : Space M) (B : Space N) :
    reindex (Equiv.sumCongr e f) (blockSum A B) = blockSum (reindex e A) (reindex f B) := by
  apply Subtype.ext
  apply Subtype.ext
  apply Matrix.ext
  intro i j
  rcases i with i | i <;> rcases j with j | j <;> rfl

theorem unitaryProjection_directSum
    (U : unitary (Matrix M M ℂ)) (V : unitary (Matrix N N ℂ)) :
    unitaryProjection (UnitaryDirectSum.inclusion (U, V)) =
      blockSum (unitaryProjection U) (unitaryProjection V) := by
  apply Subtype.ext
  apply Subtype.ext
  rw [unitaryProjection_val, blockSum_val, unitaryProjection_val, unitaryProjection_val,
    UnitaryDirectSum.inclusion_val, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply]
  simp

theorem unitaryProjection_reindex (e : M ≃ N) (U : unitary (Matrix M M ℂ)) :
    unitaryProjection ⟨Matrix.reindex e e U.val, reindex_unitary e U⟩ =
      reindex e (unitaryProjection U) := by
  apply Subtype.ext
  apply Subtype.ext
  rw [unitaryProjection_val]
  change Matrix.reindex e e U.val * (Matrix.reindex e e U.val).transpose =
    Matrix.reindex e e (unitaryProjection U).val.val
  rw [unitaryProjection_val, Matrix.transpose_reindex]
  exact ((Matrix.reindexRingEquiv ℂ e).map_mul U.val U.val.transpose).symm

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSymmetricMatrices
