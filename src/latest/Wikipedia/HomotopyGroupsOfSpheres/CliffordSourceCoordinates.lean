import Wikipedia.HomotopyGroupsOfSpheres.ComplexCliffordOutputCoordinates
import Wikipedia.HomotopyGroupsOfSpheres.CliffordBottHomotopy

/-! # Actual coordinates relating the stabilized Clifford input and the normalized Bott source -/

noncomputable section

open scoped Matrix

namespace Wikipedia.HomotopyGroupsOfSpheres.CliffordFiveHermitian

open ComplexCrossProductUnitary QuaternionicSymmetricMatrices

local notation "Padding" => Fin 2 ⊕ Fin 2
local notation "RawIndex" => Padding ⊕ (Fin 4 ⊕ Fin 4)

def paddingSplit : Fin 8 ≃ Padding ⊕ Fin 4 :=
  (finSumFinEquiv : Fin 4 ⊕ Fin 4 ≃ Fin 8).symm.trans
    (Equiv.sumCongr (finSumFinEquiv : Fin 2 ⊕ Fin 2 ≃ Fin 4).symm (Equiv.refl (Fin 4)))

def rawBlockReorderHomeomorph : Space (Fin 8 ⊕ Fin 4) ≃ₜ Space RawIndex :=
  (reindexHomeomorph (Equiv.sumCongr paddingSplit (Equiv.refl (Fin 4)))).trans
    ((reindexHomeomorph (Equiv.sumAssoc Padding (Fin 4) (Fin 4))).trans
      (reindexHomeomorph (Equiv.sumCongr (Equiv.refl Padding) (Equiv.sumComm (Fin 4) (Fin 4)))))

theorem rawBlockReorderHomeomorph_identity : rawBlockReorderHomeomorph identity = identity := by
  change reindex (Equiv.sumCongr (Equiv.refl Padding) (Equiv.sumComm (Fin 4) (Fin 4)))
    (reindex (Equiv.sumAssoc Padding (Fin 4) (Fin 4))
      (reindex (Equiv.sumCongr paddingSplit (Equiv.refl (Fin 4))) identity)) = identity
  simp only [reindex_identity]

theorem rawBlockReorderHomeomorph_embed (B : Space (Fin 4)) :
    rawBlockReorderHomeomorph (blockSum (identity : Space (Fin 8)) B) =
      blockSum (identity : Space Padding) (blockSum B (identity : Space (Fin 4))) := by
  change reindex (Equiv.sumCongr (Equiv.refl Padding) (Equiv.sumComm (Fin 4) (Fin 4)))
    (reindex (Equiv.sumAssoc Padding (Fin 4) (Fin 4))
      (reindex (Equiv.sumCongr paddingSplit (Equiv.refl (Fin 4))) (blockSum identity B))) = _
  rw [reindex_blockSum, reindex_identity, reindex_refl]
  have hi : (identity : Space (Padding ⊕ Fin 4)) = blockSum identity identity :=
    blockSum_identity.symm
  rw [hi, reindex_blockSum_assoc, reindex_blockSum, reindex_identity, reindex_blockSum_swap]

theorem blockIncludedSymmetricMap_eq_block (z : ComplexCrossProductUnitary.UnitSphere) :
    ComplexCliffordFive.blockIncludedSymmetricMap z =
      blockSum (unitaryProjection (ComplexCliffordFive.unitaryMap z))
        (identity : Space (Fin 4)) := by
  change unitaryProjection (UnitaryDirectSum.inclusion (ComplexCliffordFive.unitaryMap z, 1)) = _
  rw [unitaryProjection_directSum, unitaryProjection_one]

theorem identityPadding_eq_block (B : Space (Fin 4 ⊕ Fin 4)) :
    BalancedPhasePadding.identityPadding B =
      reindex BalancedPhasePadding.paddingIndex (blockSum (identity : Space Padding) B) :=
  Subtype.ext (Subtype.ext (BalancedPhasePadding.identityPadding_val B))

theorem rawCliffordSource_eq_block (z : ComplexCrossProductUnitary.UnitSphere) :
    rawCliffordSource z = normalizationHomeomorph
      (reindex BalancedPhasePadding.paddingIndex
        (blockSum (identity : Space Padding)
          (blockSum (unitaryProjection (ComplexCliffordFive.unitaryMap z)) identity))) := by
  change normalizationHomeomorph (BalancedPhasePadding.identityPadding
    (ComplexCliffordFive.blockIncludedSymmetricMap z)) = _
  rw [identityPadding_eq_block, blockIncludedSymmetricMap_eq_block]

def canonicalToRawHomeomorph : Space (Fin 8 ⊕ Fin 4) ≃ₜ Space (Fin 6 ⊕ Fin 6) :=
  rawBlockReorderHomeomorph.trans
    ((reindexHomeomorph BalancedPhasePadding.paddingIndex).trans normalizationHomeomorph)

theorem canonicalToRawHomeomorph_identity : canonicalToRawHomeomorph identity = identity := by
  change normalizationHomeomorph
    (reindex BalancedPhasePadding.paddingIndex (rawBlockReorderHomeomorph identity)) = identity
  rw [rawBlockReorderHomeomorph_identity, reindex_identity, normalizationHomeomorph_identity]

theorem canonicalToRawHomeomorph_embed (B : Space (Fin 4)) :
    canonicalToRawHomeomorph (blockSum (identity : Space (Fin 8)) B) =
      normalizationHomeomorph (reindex BalancedPhasePadding.paddingIndex
        (blockSum (identity : Space Padding) (blockSum B identity))) := by
  change normalizationHomeomorph (reindex BalancedPhasePadding.paddingIndex
    (rawBlockReorderHomeomorph (blockSum identity B))) = _
  rw [rawBlockReorderHomeomorph_embed]

def targetCoordinateHomeomorph : Space (Fin (3 + 9)) ≃ₜ Space (Fin 6 ⊕ Fin 6) :=
  ComplexCliffordFive.stabilizedOutputHomeomorph.trans canonicalToRawHomeomorph

theorem targetCoordinateHomeomorph_identity : targetCoordinateHomeomorph identity = identity := by
  change canonicalToRawHomeomorph (ComplexCliffordFive.stabilizedOutputHomeomorph identity) = _
  rw [ComplexCliffordFive.stabilizedOutputHomeomorph_identity, canonicalToRawHomeomorph_identity]

theorem targetCoordinateHomeomorph_apply (z : ComplexCrossProductUnitary.UnitSphere) :
    targetCoordinateHomeomorph (ComplexCliffordFive.stableCliffordInput z) =
      rawCliffordSource (ComplexCliffordFive.parameterHomeomorph z) := by
  change canonicalToRawHomeomorph
    (ComplexCliffordFive.stabilizedOutputHomeomorph (ComplexCliffordFive.stableCliffordInput z)) = _
  rw [ComplexCliffordFive.stabilizedOutputHomeomorph_apply, canonicalToRawHomeomorph_embed,
    ← rawCliffordSource_eq_block]

end Wikipedia.HomotopyGroupsOfSpheres.CliffordFiveHermitian
