/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SplitGroundingGroundedRelevantCutAvoidingFailure
import ErdosProblems.Erdos599.SplitGroundingGroundedFreshAvoidingCanonical

/-!
# Relevant source-first dispatcher for the canonical fresh-avoiding controls

This is the exact specialization consumed by the canonical separator branch.
The final controls and unused record are the canonical fresh-avoiding objects,
and the record's whole cut-trace avoidance is discharged by its construction.
-/

noncomputable section

open Cardinal Set

namespace Erdos599

open DirectedPath

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

namespace DWeb.KappaLadder

variable {L : Gamma.KappaLadder kappa} {hL : L.IsSplitKappaHindrance}
  {hground : Stationary.IsStationaryBelow kappa L.phiGround}
  {hnotFresh : ¬ Stationary.IsStationaryBelow kappa
    L.freshInessentialGroundStages}
  {S : Popular.PopularSeparator
    (L.splitGroundedPopularAuxiliaryIndexed hL hground)}

private abbrev FreshRelevantControls :=
  L.splitGroundedFreshAvoidingCanonicalControls hL hground hnotFresh S

private abbrev FreshRelevantRecord :=
  L.splitGroundedFreshAvoidingCanonicalUnusedRecord
    hL hground hnotFresh S

/-- Canonical fresh-avoiding source-first normalization.  There is no
record-choice, control-root, or reserved-endpoint premise. -/
theorem exists_hindrance_or_splitGroundedFreshAvoidingRelevantFailure
    (hC : Popular.IsSeparator
      (L.splitGroundedPopularAuxiliaryInput hL.legal).lambda S.cut) :
    (∃ W : Set Gamma.DPath, Gamma.IsHindrance W) ∨
      ∃ t ∈ L.splitGroundedRelevantSourceFirstBB hL.legal S.cut,
        SplitGroundedUnusedRecord.SplitGroundedRelevantCutAvoidingFailureAt
          (FreshRelevantRecord (L := L) (hL := hL)
            (hground := hground) (hnotFresh := hnotFresh) (S := S)) t := by
  let R := FreshRelevantRecord (L := L) (hL := hL)
    (hground := hground) (hnotFresh := hnotFresh) (S := S)
  exact R.exists_hindrance_or_splitGroundedRelevantCutAvoidingFailure
    (L.splitGroundedFreshAvoidingCanonicalUnusedRecord_trace_disjoint
      hL hground hnotFresh S) hC

end DWeb.KappaLadder
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.exists_hindrance_or_splitGroundedFreshAvoidingRelevantFailure
