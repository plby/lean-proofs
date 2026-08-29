/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SplitGroundingGroundedLastContactComponentSplice
import ErdosProblems.Erdos599.SplitGroundingGroundedSourceRecordCutAvoiding

/-!
# Frontier preservation for a cut-avoiding source-record splice

Once the old owner of a literal last-contact splice is identified with the
grounded record represented by its selected auxiliary source, full
source-carrier avoidance of the popular cut makes the discarded owner tail
irrelevant to the source-correct boundary.  Every relevant-boundary point of
the replacement component therefore lies on the normalized selected suffix.
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
  {S : Popular.PopularSeparator
    (L.splitGroundedPopularAuxiliaryIndexed hL hground)}
  {K : GroundingSelection.Controls S}

/-- The concrete frontier-preservation consequence of identifying a splice
owner with a selected source's cut-avoiding grounded record. -/
theorem SplitGroundedLastContactComponentSplice.relevantFrontier_mem_suffix_of_sourceRecord
    (X : SplitGroundedLastContactComponentSplice
      (L := L) (hL := hL) (hground := hground) (S := S) (K := K)
        (L.splitGroundedRelevantSourceFirstBB hL.legal S.cut))
    (xsource : (L.splitGroundedPopularAuxiliaryInput hL.legal).lambda.source)
    (R : L.SplitGroundedAuxiliarySourceRecord hL.legal xsource)
    (hcarrier : Disjoint
      (PopularSwitching.ladderTrace
        (L.splitGroundedPopularAuxiliaryInput hL.legal) R.record ∪
          {xsource.1}) S.cut)
    (howner : X.oldOwner = R.record)
    {b : V}
    (hbB : b ∈ L.splitGroundedRelevantSourceFirstBB hL.legal S.cut)
    (hb : b ∈ X.replacementCarrier) :
    b ∈ X.contact.normalizedSuffix.path.vertexSet := by
  have hB : Disjoint
      (L.splitGroundedRelevantSourceFirstBB hL.legal S.cut)
      R.record.support :=
    (R.relevantBB_disjoint_record_of_ownCarrier_disjoint
      xsource hcarrier).mono_left
        (L.splitGroundedRelevantSourceFirstBB_subset hL.legal S.cut)
  apply X.frontier_mem_normalizedSuffix
    (B := L.splitGroundedRelevantSourceFirstBB hL.legal S.cut)
  · simpa only [howner] using hB
  · exact hbB
  · exact hb

end DWeb.KappaLadder
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.SplitGroundedLastContactComponentSplice.relevantFrontier_mem_suffix_of_sourceRecord
