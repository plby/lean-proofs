/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SplitGroundingGroundedRootProvenance
import ErdosProblems.Erdos599.GroundingErasedDecode

/-!
# The unused grounded split record is not a selected attachment owner

Stationary subtraction says that no selected request starts at the
auxiliary source representing the reserved record.  Source injectivity and
warp disjointness upgrade this to the concrete statement needed by the
simultaneous relation: no selected decoded trace starts on that record.
Consequently proxy-prefix repair never deletes an edge of the record.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599

open DirectedPath PopularGroundingBridge
open GroundingSimultaneousDecode GroundingErasedDecode

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

namespace DWeb.KappaLadder.SplitGroundedUnusedRecord

variable {L : Gamma.KappaLadder kappa} {hL : L.IsSplitKappaHindrance}
  {hground : Stationary.IsStationaryBelow kappa L.phiGround}
  {S : Popular.PopularSeparator
    (L.splitGroundedPopularAuxiliaryIndexed hL hground)}
  {K : GroundingSelection.Controls S}

private abbrev J := L.splitGroundedPopularAuxiliaryInput hL.legal
private abbrev U := L.splitGroundedPopularAuxiliaryIndexed hL hground

/-- The initial point of no selected decoded request trace lies on the
reserved limiting-ladder record. -/
theorem selectedRequestTrace_initial_not_mem_record_support
    (R : L.SplitGroundedUnusedRecord hL hground S K)
    (r : Request (J (L := L) (hL := hL)) S.cut) :
    (selectedRequestTrace (U (L := L) (hL := hL)
      (hground := hground)) S K r).initial ∉ R.record.support := by
  intro hcontact
  obtain ⟨a, parent, _haGround, hchosen, hparentInessential,
    hparentContact, _hparentSource, hindex⟩ :=
      L.splitGroundedSelectedRequestTrace_grounded_record_data
        hL hground S K r
  have hparentRecord : parent = R.record :=
    Alternating.DWeb.IsWarp.eq_of_mem_support
      (hL.legal.warpStages (Ladder.finalStage kappa))
      hparentInessential.1 R.limit_inessential.1
      hparentContact hcontact
  have ha : a = R.stage := by
    apply L.bookkeeping.chosen_stage_unique hL.legal.validBookkeeping
    · exact hchosen
    · rw [hparentRecord]
      exact R.chosen
  apply R.stage_unused
  let W := strongSelectedWarp
    (U (L := L) (hL := hL) (hground := hground)) S K
  let p := strongSelectedPath
    (U (L := L) (hL := hL) (hground := hground)) S K r
  have hp : p ∈ W.paths := ⟨r, rfl⟩
  refine ⟨p, hp, ?_⟩
  exact hindex.symm.trans ha

/-- Proxy-prefix repair never deletes a directed edge belonging to the
reserved record. -/
theorem record_edge_not_mem_attachmentCutEdges
    (R : L.SplitGroundedUnusedRecord hL hground S K) {e : V × V}
    (he : e ∈ R.record.edgeSet) :
    e ∉ attachmentCutEdges
      (U (L := L) (hL := hL) (hground := hground)) S K := by
  intro heAttachment
  obtain ⟨c, hr⟩ := heAttachment.2
  apply R.selectedRequestTrace_initial_not_mem_record_support
    (chosenRequest c)
  rw [← hr]
  exact (R.record.edgeSet_subset_support_prod he).1

/-- Set-valued form of reserved-record attachment nondeletion. -/
theorem record_edgeSet_disjoint_attachmentCutEdges
    (R : L.SplitGroundedUnusedRecord hL hground S K) :
    Disjoint R.record.edgeSet
      (attachmentCutEdges
        (U (L := L) (hL := hL) (hground := hground)) S K) := by
  rw [Set.disjoint_left]
  exact fun _ he ↦ R.record_edge_not_mem_attachmentCutEdges he

end DWeb.KappaLadder.SplitGroundedUnusedRecord
end Erdos599

#print axioms Erdos599.DWeb.KappaLadder.SplitGroundedUnusedRecord.selectedRequestTrace_initial_not_mem_record_support
#print axioms Erdos599.DWeb.KappaLadder.SplitGroundedUnusedRecord.record_edgeSet_disjoint_attachmentCutEdges
