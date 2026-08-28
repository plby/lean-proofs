import Wikipedia.HomotopyGroupsOfSpheres.ComplexCliffordStableHomotopy
import Wikipedia.HomotopyGroupsOfSpheres.MatrixStabilizationCoordinates
import Wikipedia.HomotopyGroupsOfSpheres.SymmetricUnitaryBlockPermutations

/-! # Removing the original Clifford output coordinates by actual based homeomorphisms -/

noncomputable section

open scoped Matrix

namespace Wikipedia.HomotopyGroupsOfSpheres.ComplexCliffordFive

open ComplexCrossProductUnitary QuaternionicSymmetricMatrices

local notation "BlockIndex" => Fin 3 ⊕ Fin 1

def outputFrame (r : ℕ) : unitary (Matrix (Fin r ⊕ BlockIndex) (Fin r ⊕ BlockIndex) ℂ) :=
  UnitaryDirectSum.inclusion (1, blockLeft)

theorem outputFrame_real (r : ℕ) (i j : Fin r ⊕ BlockIndex) :
    star ((outputFrame r).val i j) = (outputFrame r).val i j :=
  UnitaryDirectSum.inclusion_real 1 blockLeft
    (by intro a b; simp [Matrix.one_apply]) blockLeftMatrix_real i j

def outputExtensionHomeomorph (r : ℕ) :
    Space (Fin r ⊕ BlockIndex) ≃ₜ Space (Fin r ⊕ Fin 4) :=
  (congruenceSpaceHomeomorph (outputFrame r)).trans
    (reindexHomeomorph (Equiv.sumCongr (Equiv.refl (Fin r)) frontIndex))

theorem outputExtensionHomeomorph_identity (r : ℕ) :
    outputExtensionHomeomorph r identity = identity := by
  change reindexHomeomorph _ (congruenceSpaceHomeomorph (outputFrame r) identity) = identity
  rw [congruenceSpaceHomeomorph_identity _ (outputFrame_real r), reindexHomeomorph_identity]

theorem outputExtensionHomeomorph_embed (r : ℕ) (B : Space BlockIndex) :
    outputExtensionHomeomorph r (blockSum (identity : Space (Fin r)) B) =
      blockSum identity (outputTransform B) := by
  change reindex (Equiv.sumCongr (Equiv.refl (Fin r)) frontIndex)
    (congruence (UnitaryDirectSum.inclusion (1, blockLeft)) (blockSum identity B)) = _
  rw [congruence_blockSum, congruence_one, reindex_blockSum, reindex_identity]
  rfl

theorem outputExtensionHomeomorph_symm_embed (r : ℕ) (B : Space BlockIndex) :
    (outputExtensionHomeomorph r).symm (blockSum identity (outputTransform B)) =
      blockSum identity B := by
  rw [← outputExtensionHomeomorph_embed, Homeomorph.symm_apply_apply]

def unoutputHomeomorph (r : ℕ) : Space (Fin r ⊕ Fin 4) ≃ₜ Space (Fin r ⊕ Fin 4) :=
  (outputExtensionHomeomorph r).symm.trans
    (reindexHomeomorph (Equiv.sumCongr (Equiv.refl (Fin r)) blockIndex))

theorem unoutputHomeomorph_identity (r : ℕ) : unoutputHomeomorph r identity = identity := by
  have h : (outputExtensionHomeomorph r).symm identity = identity := by
    rw [← outputExtensionHomeomorph_identity r, Homeomorph.symm_apply_apply]
  change reindex _ ((outputExtensionHomeomorph r).symm identity) = identity
  rw [h, reindex_identity]

theorem unoutputHomeomorph_embed (r : ℕ) (B : Space (Fin 4)) :
    unoutputHomeomorph r
      (blockSum identity (outputTransform (reindex blockIndex.symm B))) = blockSum identity B := by
  change reindex _ ((outputExtensionHomeomorph r).symm
    (blockSum identity (outputTransform (reindex blockIndex.symm B)))) = _
  rw [outputExtensionHomeomorph_symm_embed, reindex_blockSum, reindex_identity]
  have h : reindex blockIndex (reindex blockIndex.symm B) = B :=
    reindex_symm_reindex blockIndex.symm B
  rw [h]

attribute [local irreducible] parameterHomeomorph unitaryMap

theorem blockSymmetricClifford_reindex (z : UnitSphere) :
    blockSymmetricClifford z = reindex blockIndex.symm (unitaryProjection (unitaryMap z)) :=
  unitaryProjection_reindex blockIndex.symm (unitaryMap z)

def stabilizedOutputHomeomorph : Space (Fin (3 + 9)) ≃ₜ Space (Fin 8 ⊕ Fin 4) :=
  (MatrixStabilizationCoordinates.modelHomeomorph 4 8).symm.trans (unoutputHomeomorph 8)

theorem stabilizedOutputHomeomorph_identity : stabilizedOutputHomeomorph identity = identity := by
  have h : (MatrixStabilizationCoordinates.modelHomeomorph 4 8).symm identity = identity := by
    rw [← MatrixStabilizationCoordinates.modelHomeomorph_identity 4 8,
      Homeomorph.symm_apply_apply]
  change unoutputHomeomorph 8
    ((MatrixStabilizationCoordinates.modelHomeomorph 4 8).symm identity) = _
  rw [h, unoutputHomeomorph_identity]

theorem stabilizedOutputHomeomorph_apply (z : UnitSphere) :
    stabilizedOutputHomeomorph (stableCliffordInput z) =
      blockSum (identity : Space (Fin 8))
        (unitaryProjection (unitaryMap (parameterHomeomorph z))) := by
  change unoutputHomeomorph 8 ((MatrixStabilizationCoordinates.modelHomeomorph 4 8).symm
    (stabilizationIterate 4 8 (cliffordInput z))) = _
  rw [MatrixStabilizationCoordinates.modelHomeomorph_symm_stabilization]
  change unoutputHomeomorph 8
    (blockSum identity (outputTransform (blockSymmetricClifford (parameterHomeomorph z)))) = _
  rw [blockSymmetricClifford_reindex, unoutputHomeomorph_embed]

end Wikipedia.HomotopyGroupsOfSpheres.ComplexCliffordFive
