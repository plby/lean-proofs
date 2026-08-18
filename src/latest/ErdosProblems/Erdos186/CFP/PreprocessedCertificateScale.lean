/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.PreprocessedWitness

/-!
# Weakening the fixed scale denominator of a reserve certificate

Increasing the denominator only weakens the lower scale comparison.  This
small transport lets the finite set of possible retained ranks share one
source-facing scale denominator.
-/

namespace Erdos186.CFP

noncomputable section

namespace PreprocessedReserveCertificate

/-- Enlarge the allowed core loss without changing the finite witness. -/
def increaseLoss
    {stableCore : Finset ℤ}
    {s D extraLoss extraLoss' scaleNum scaleDen : ℕ}
    (C : PreprocessedReserveCertificate stableCore s D extraLoss
      scaleNum scaleDen)
    (hle : extraLoss ≤ extraLoss') :
    PreprocessedReserveCertificate stableCore s D extraLoss'
      scaleNum scaleDen where
  integerCore := C.integerCore
  integerCore_subset := C.integerCore_subset
  stableCore_large := C.stableCore_large.trans
    (Nat.add_le_add_left hle C.integerCore.card)
  ell := C.ell
  rank := C.rank
  k := C.k
  reserve := C.reserve
  progression := C.progression
  translatePoint := C.translatePoint
  reserve_pairwiseDisjoint := C.reserve_pairwiseDisjoint
  rank_le := C.rank_le
  reserve_subset_core := C.reserve_subset_core
  reserve_small := C.reserve_small
  core_zero_subset := C.core_zero_subset
  homogeneous := C.homogeneous
  covered := C.covered
  dilate_proper := C.dilate_proper
  k_pos := C.k_pos
  scaleNum_pos := C.scaleNum_pos
  scaleDen_pos := C.scaleDen_pos
  scale_lower := C.scale_lower
  scale_upper := C.scale_upper
  progression_proper := C.progression_proper
  progression_symmetric := C.progression_symmetric
  progression_nondegenerate := C.progression_nondegenerate
  covered_translate_homogeneous := C.covered_translate_homogeneous

/-- Replace the scale denominator by a larger positive denominator. -/
def increaseScaleDen
    {stableCore : Finset ℤ}
    {s D extraLoss scaleNum scaleDen scaleDen' : ℕ}
    (C : PreprocessedReserveCertificate stableCore s D extraLoss
      scaleNum scaleDen)
    (hle : scaleDen ≤ scaleDen') (hpos : 0 < scaleDen') :
    PreprocessedReserveCertificate stableCore s D extraLoss
      scaleNum scaleDen' where
  integerCore := C.integerCore
  integerCore_subset := C.integerCore_subset
  stableCore_large := C.stableCore_large
  ell := C.ell
  rank := C.rank
  k := C.k
  reserve := C.reserve
  progression := C.progression
  translatePoint := C.translatePoint
  reserve_pairwiseDisjoint := C.reserve_pairwiseDisjoint
  rank_le := C.rank_le
  reserve_subset_core := C.reserve_subset_core
  reserve_small := C.reserve_small
  core_zero_subset := C.core_zero_subset
  homogeneous := C.homogeneous
  covered := C.covered
  dilate_proper := C.dilate_proper
  k_pos := C.k_pos
  scaleNum_pos := C.scaleNum_pos
  scaleDen_pos := hpos
  scale_lower := C.scale_lower.trans (Nat.mul_le_mul_right C.k hle)
  scale_upper := C.scale_upper
  progression_proper := C.progression_proper
  progression_symmetric := C.progression_symmetric
  progression_nondegenerate := C.progression_nondegenerate
  covered_translate_homogeneous := C.covered_translate_homogeneous

end PreprocessedReserveCertificate

end

end Erdos186.CFP

#print axioms
  Erdos186.CFP.PreprocessedReserveCertificate.increaseScaleDen
#print axioms Erdos186.CFP.PreprocessedReserveCertificate.increaseLoss
