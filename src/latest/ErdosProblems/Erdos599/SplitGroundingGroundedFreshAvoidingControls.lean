/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SplitGroundingEqualPriorCollision
import ErdosProblems.Erdos599.SplitGroundingGroundedReservedControls
import ErdosProblems.Erdos599.SplitGroundingGroundedCutAvoidingSelection
import ErdosProblems.Erdos599.GroundingSourceCarrierControls

/-!
# Grounded controls after removing the fresh diagonal

If the genuinely successor-new grounded stages are nonstationary, the
matched-stage remainder of Assertion 8.19 is nonstationary at every request.
It can therefore be adjoined to the fragment-exceptional family.  The
resulting selected paths avoid every original hanging ladder component, not
merely the strict-owner subfamily.

The second half of the file reapplies the reserved-record carrier avoidance
to an arbitrary base control package.  This is needed because the earlier
reserved refinement was hard-coded to the strict controls.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace DWeb
namespace KappaLadder

open _root_.Erdos599.DirectedPath Stationary PopularGroundingBridge
open GroundingSimultaneousDecode

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

variable {L : Gamma.KappaLadder kappa} {hL : L.IsSplitKappaHindrance}
  {hground : IsStationaryBelow kappa L.phiGround}
  {S : Popular.PopularSeparator
    (L.splitGroundedPopularAuxiliaryIndexed hL hground)}

private abbrev FreshAvoidingInput :=
  L.splitGroundedPopularAuxiliaryInput hL.legal

private abbrev FreshAvoidingIndexed :=
  L.splitGroundedPopularAuxiliaryIndexed hL hground

/-- Under nonstationarity of the fresh grounded diagonal, forbid every
literal hanging-ladder collision.  The strict collisions retain their
regressive-rank slot; the matched-stage remainder is placed in the
independently nonstationary fragment slot. -/
noncomputable def splitGroundedFreshAvoidingControls
    (hnotFresh : ¬ IsStationaryBelow kappa
      L.freshInessentialGroundStages) :
    GroundingSelection.Controls S :=
  let K := (L.splitGroundedControls hL hground S).withSourceCarrierCutAvoidance
    (L.splitGroundedSourceCarrierFamily hL.legal)
  {
    hangingLadder := K.hangingLadder
    hangingFragment := fun r ↦ K.hangingFragment r ∪
      {p | GroundingConcreteControls.hangingLadderCollision
        (FreshAvoidingInput (L := L) (hL := hL)) S.cut r p}
    ladderRank := K.ladderRank
    ladderTrace := K.ladderTrace
    ladderRank_regressive := K.ladderRank_regressive
    ladderTrace_countable := K.ladderTrace_countable
    ladderTrace_disjoint_apex := K.ladderTrace_disjoint_apex
    hangingLadder_meets := K.hangingLadder_meets
    fragmentIndices_nonstationary := by
      intro r
      have hbase := K.fragmentIndices_nonstationary r
      have hcollision : ¬ IsStationaryBelow kappa
          (L.splitGroundedAssertion819CollisionIndices
            hL hground S r) := by
        intro hstationary
        exact hnotFresh
          (L.freshInessentialGroundStages_isStationary_of_splitGrounded_collisions
            hL hground S r hstationary)
      intro hstationary
      apply GroundingSelection.not_isStationaryBelow_union
        hL.legal.regular hL.legal.uncountable hbase hcollision
      exact hstationary.mono
        (GroundingControlledAssembly.restrictedIndices_union_subset
          (FreshAvoidingIndexed (L := L) (hL := hL)
            (hground := hground))
          (requestFan S r) (K.hangingFragment r)
          {p | GroundingConcreteControls.hangingLadderCollision
            (FreshAvoidingInput (L := L) (hL := hL)) S.cut r p})
  }

/-- Every path selected by the fresh-avoiding controls is disjoint from the
full original-hanging collision predicate of Assertion 8.19. -/
theorem splitGroundedFreshAvoidingStrongSelectedPath_no_hangingCollision
    (hnotFresh : ¬ IsStationaryBelow kappa
      L.freshInessentialGroundStages)
    (r : Request (FreshAvoidingInput (L := L) (hL := hL)) S.cut) :
    ¬ GroundingConcreteControls.hangingLadderCollision
      (FreshAvoidingInput (L := L) (hL := hL)) S.cut r
      (strongSelectedPath
        (FreshAvoidingIndexed (L := L) (hL := hL) (hground := hground)) S
        (splitGroundedFreshAvoidingControls (L := L) (hL := hL)
          (hground := hground) (S := S) hnotFresh) r) := by
  intro hcollision
  apply strongSelectedPath_not_mem_hangingFragment
    (FreshAvoidingIndexed (L := L) (hL := hL) (hground := hground)) S
    (splitGroundedFreshAvoidingControls (L := L) (hL := hL)
      (hground := hground) (S := S) hnotFresh) r
  exact Or.inr hcollision

/-! ## Re-reserving an arbitrary refined control package -/

variable {K : GroundingSelection.Controls S}

/-- Add the already-proved off-apex reserved-record avoidance to an
arbitrary grounded control package. -/
noncomputable def splitGroundedReservedControlsFrom
    (R : L.SplitGroundedUnusedRecord hL hground S K) :
    GroundingSelection.Controls S :=
  {
    hangingLadder := K.hangingLadder
    hangingFragment := fun r ↦ K.hangingFragment r ∪
      splitGroundedReservedRecordCollidingPaths R r
    ladderRank := K.ladderRank
    ladderTrace := K.ladderTrace
    ladderRank_regressive := K.ladderRank_regressive
    ladderTrace_countable := K.ladderTrace_countable
    ladderTrace_disjoint_apex := K.ladderTrace_disjoint_apex
    hangingLadder_meets := K.hangingLadder_meets
    fragmentIndices_nonstationary := by
      intro r
      have hbase := K.fragmentIndices_nonstationary r
      have hreserved :=
        splitGroundedReservedRecordCollidingIndices_nonstationary R r
      intro hstationary
      apply GroundingSelection.not_isStationaryBelow_union
        hL.legal.regular hL.legal.uncountable hbase hreserved
      exact hstationary.mono
        (GroundingControlledAssembly.restrictedIndices_union_subset
          (FreshAvoidingIndexed (L := L) (hL := hL)
            (hground := hground))
          (requestFan S r) (K.hangingFragment r)
          (splitGroundedReservedRecordCollidingPaths R r))
  }

/-- A selected request route for the generic reserved refinement avoids the
reserved record away from its own request apex. -/
theorem splitGroundedReservedControlsFrom_no_offApex_contact
    (R : L.SplitGroundedUnusedRecord hL hground S K)
    (r : Request (FreshAvoidingInput (L := L) (hL := hL)) S.cut)
    {x : PopularAuxiliary.Input.LambdaVertex V L.groundedInfiniteRecords}
    (hxCarrier : x ∈ splitGroundedReservedRecordCarrier R)
    (hxApex : x ≠ requestAuxVertex r) :
    x ∉ (strongSelectedPath
      (FreshAvoidingIndexed (L := L) (hL := hL) (hground := hground)) S
      (splitGroundedReservedControlsFrom R) r).support := by
  intro hxPath
  apply strongSelectedPath_not_mem_hangingFragment
    (FreshAvoidingIndexed (L := L) (hL := hL) (hground := hground)) S
    (splitGroundedReservedControlsFrom R) r
  exact Or.inr ⟨x, ⟨hxCarrier, by
    simpa only [Set.mem_singleton_iff]⟩, hxPath⟩

/-- In particular, the generic reserved selector never reuses the omitted
record's auxiliary source. -/
theorem splitGroundedReservedControlsFrom_start_ne_reservedSource
    (R : L.SplitGroundedUnusedRecord hL hground S K)
    (r : Request (FreshAvoidingInput (L := L) (hL := hL)) S.cut) :
    (strongSelectedPath
      (FreshAvoidingIndexed (L := L) (hL := hL) (hground := hground)) S
      (splitGroundedReservedControlsFrom R) r).start ≠
      R.auxiliarySource.1 := by
  intro hstart
  apply splitGroundedReservedControlsFrom_no_offApex_contact R r
    (Or.inr (Set.mem_singleton R.auxiliarySource.1))
  · intro heq
    apply R.auxiliarySource_not_mem_cut
    rw [heq]
    exact requestAuxVertex_mem_cut r
  · rw [← hstart]
    exact (strongSelectedPath
      (FreshAvoidingIndexed (L := L) (hL := hL) (hground := hground)) S
      (splitGroundedReservedControlsFrom R) r).start_mem_support

/-- The omitted stage for the base controls remains omitted after the
generic reserved refinement. -/
theorem SplitGroundedUnusedRecord.stage_unused_reservedControlsFrom
    (R : L.SplitGroundedUnusedRecord hL hground S K) :
    R.stage ∉ Popular.initialIndicesOf
      (FreshAvoidingIndexed (L := L) (hL := hL) (hground := hground))
      (strongSelectedWarp
        (FreshAvoidingIndexed (L := L) (hL := hL) (hground := hground)) S
        (splitGroundedReservedControlsFrom R)).paths
      (strongSelectedWarp
        (FreshAvoidingIndexed (L := L) (hL := hL) (hground := hground)) S
        (splitGroundedReservedControlsFrom R)).starts_in_source := by
  rintro ⟨p, hp, hpindex⟩
  obtain ⟨r, rfl⟩ := hp
  let U := FreshAvoidingIndexed (L := L) (hL := hL) (hground := hground)
  let W := strongSelectedWarp U S (splitGroundedReservedControlsFrom R)
  let q := strongSelectedPath U S (splitGroundedReservedControlsFrom R) r
  have hqW : q ∈ W.paths := ⟨r, rfl⟩
  have hsourceEq :
      (⟨q.start, W.starts_in_source hqW⟩ :
        (FreshAvoidingInput (L := L) (hL := hL)).lambda.source) =
        R.auxiliarySource := by
    apply L.splitGroundedPopularAuxiliaryIndexed_sourceIndexed hL hground
    exact hpindex.trans R.source_index.symm
  exact splitGroundedReservedControlsFrom_start_ne_reservedSource R r
    (congrArg Subtype.val hsourceEq)

/-- Repackage the same record for the arbitrary refined-and-reserved
controls. -/
noncomputable def SplitGroundedUnusedRecord.forReservedControlsFrom
    (R : L.SplitGroundedUnusedRecord hL hground S K) :
    L.SplitGroundedUnusedRecord hL hground S
      (splitGroundedReservedControlsFrom R) where
  stage := R.stage
  stage_ground := R.stage_ground
  stage_unused := R.stage_unused_reservedControlsFrom
  record := R.record
  chosen := R.chosen
  grounded := R.grounded
  limit_inessential := R.limit_inessential
  auxiliarySource := R.auxiliarySource
  source_index := R.source_index
  auxiliarySource_not_mem_cut := R.auxiliarySource_not_mem_cut
  source_represents := R.source_represents

/-- Reserving a record does not reintroduce any full hanging collision
for the fresh-avoiding controls. -/
theorem splitGroundedFreshAvoidingReservedStrongSelectedPath_no_hangingCollision
    (hnotFresh : ¬ IsStationaryBelow kappa
      L.freshInessentialGroundStages)
    (R : L.SplitGroundedUnusedRecord hL hground S
      (splitGroundedFreshAvoidingControls (L := L) (hL := hL)
        (hground := hground) (S := S) hnotFresh))
    (r : Request (FreshAvoidingInput (L := L) (hL := hL)) S.cut) :
    ¬ GroundingConcreteControls.hangingLadderCollision
      (FreshAvoidingInput (L := L) (hL := hL)) S.cut r
      (strongSelectedPath
        (FreshAvoidingIndexed (L := L) (hL := hL) (hground := hground)) S
        (splitGroundedReservedControlsFrom R) r) := by
  intro hcollision
  apply strongSelectedPath_not_mem_hangingFragment
    (FreshAvoidingIndexed (L := L) (hL := hL) (hground := hground)) S
    (splitGroundedReservedControlsFrom R) r
  exact Or.inl (Or.inr hcollision)

/-- The omitted record cannot be the limiting-ladder owner of a backward
link selected after the generic reserved refinement. -/
theorem splitGroundedReservedControlsFrom_backward_parent_ne_record
    (R : L.SplitGroundedUnusedRecord hL hground S K)
    (r : Request (FreshAvoidingInput (L := L) (hL := hL)) S.cut)
    (l : Alternating.Link Gamma.graph)
    (hl : l ∈ (GroundingErasedDecode.selectedErasedCompression
      (FreshAvoidingIndexed (L := L) (hL := hL) (hground := hground)) S
      (splitGroundedReservedControlsFrom R) r).path.links)
    (hldir : l.direction = .backward)
    (parent : Gamma.DPath) (_hparent : parent ∈ L.limitWarp)
    (hsub : l.path.IsSubpathOf parent) :
    parent ≠ R.record := by
  intro hparentRecord
  subst parent
  obtain ⟨y, hy⟩ :=
    _root_.Erdos599.Alternating.FinitePath.exists_outgoing_edge_of_mem_support_of_ne_finish
      l.path l.path.start_mem_support l.nontrivial
  have heDirection : (l.path.start, y) ∈
      (GroundingErasedDecode.selectedErasedCompression
        (FreshAvoidingIndexed (L := L) (hL := hL) (hground := hground)) S
        (splitGroundedReservedControlsFrom R) r).path.directionEdges
          .backward := by
    simp only [Alternating.AltPath.directionEdges, Set.mem_iUnion]
    exact ⟨l, hl, hldir, hy⟩
  obtain ⟨hePath, heOffApex⟩ :=
    selectedBackwardEdge_auxContact_offApex_split
      (FreshAvoidingIndexed (L := L) (hL := hL) (hground := hground)) S
      (splitGroundedReservedControlsFrom R) r heDirection
  have heCarrier :
      (PopularAuxiliary.Input.LambdaVertex.edge l.path.start y :
        (FreshAvoidingInput (L := L) (hL := hL)).LV) ∈
        splitGroundedReservedRecordCarrier R := by
    left
    right
    exact ⟨(l.path.start, y), hsub.2 hy, rfl⟩
  exact splitGroundedReservedControlsFrom_no_offApex_contact
    R r heCarrier heOffApex hePath

/-- Once the fresh diagonal is nonstationary, every selected backward owner
has an actual finite prefix from an allowed original source.  The hanging
equal-stage alternative has been removed from the selector itself. -/
theorem splitGroundedFreshAvoidingReservedBackwardOwner_rootPrefix
    (hnotFresh : ¬ IsStationaryBelow kappa
      L.freshInessentialGroundStages)
    (R : L.SplitGroundedUnusedRecord hL hground S
      (splitGroundedFreshAvoidingControls (L := L) (hL := hL)
        (hground := hground) (S := S) hnotFresh))
    (r : Request (FreshAvoidingInput (L := L) (hL := hL)) S.cut)
    (l : Alternating.Link Gamma.graph)
    (hl : l ∈ (GroundingErasedDecode.selectedErasedCompression
      (FreshAvoidingIndexed (L := L) (hL := hL) (hground := hground)) S
      (splitGroundedReservedControlsFrom R) r).path.links)
    (hldir : l.direction = .backward)
    (parent : Gamma.DPath) (hparent : parent ∈ L.limitWarp)
    (hsub : l.path.IsSubpathOf parent) :
    ∃ q : FinitePath Gamma.graph,
      q.start ∈ Gamma.source \ {R.record.initial} ∧
      q.finish = l.path.start ∧ q.support ⊆ parent.support ∧
      q.edgeSet ⊆ parent.edgeSet := by
  have hne : parent ≠ R.record :=
    splitGroundedReservedControlsFrom_backward_parent_ne_record
      R r l hl hldir parent hparent hsub
  by_cases hgrounded : PopularAuxiliary.IsGroundedPath Gamma parent
  · have hrootNe : parent.initial ≠ R.record.initial := by
      intro heq
      apply hne
      apply Alternating.DWeb.IsWarp.eq_of_mem_support
        (hL.legal.warpStages (Ladder.finalStage kappa)) hparent
        R.limit_inessential.1
      · exact parent.initial_mem_support
      · rw [heq]
        exact R.record.initial_mem_support
    obtain ⟨q, hqStart, hqFinish, hqSupport, hqEdges⟩ :=
      GroundingPathPrefix.exists_initialFinitePrefix parent
        (hsub.1 l.path.start_mem_support)
    refine ⟨q, ?_, hqFinish, hqSupport, hqEdges⟩
    rw [hqStart]
    exact ⟨hgrounded, fun heq ↦
      hrootNe (Set.mem_singleton_iff.mp heq)⟩
  · exfalso
    obtain ⟨y, hy⟩ :=
      _root_.Erdos599.Alternating.FinitePath.exists_outgoing_edge_of_mem_support_of_ne_finish
        l.path l.path.start_mem_support l.nontrivial
    have heDirection : (l.path.start, y) ∈
        (GroundingErasedDecode.selectedErasedCompression
          (FreshAvoidingIndexed (L := L) (hL := hL)
            (hground := hground)) S
          (splitGroundedReservedControlsFrom R) r).path.directionEdges
            .backward := by
      simp only [Alternating.AltPath.directionEdges, Set.mem_iUnion]
      exact ⟨l, hl, hldir, hy⟩
    obtain ⟨hePath, heOffApex⟩ :=
      selectedBackwardEdge_auxContact_offApex_split
        (FreshAvoidingIndexed (L := L) (hL := hL)
          (hground := hground)) S
        (splitGroundedReservedControlsFrom R) r heDirection
    have hcollision : GroundingConcreteControls.hangingLadderCollision
        (FreshAvoidingInput (L := L) (hL := hL)) S.cut r
        (strongSelectedPath
          (FreshAvoidingIndexed (L := L) (hL := hL)
            (hground := hground)) S
          (splitGroundedReservedControlsFrom R) r) := by
      refine ⟨parent, ⟨?_, hgrounded⟩,
        PopularAuxiliary.Input.LambdaVertex.edge l.path.start y, ?_, hePath⟩
      · simpa only [splitGroundedPopularAuxiliaryInput] using hparent
      · exact ⟨Or.inr ⟨(l.path.start, y), hsub.2 hy, rfl⟩, by
          simpa only [Set.mem_singleton_iff] using heOffApex⟩
    exact
      (splitGroundedFreshAvoidingReservedStrongSelectedPath_no_hangingCollision
        hnotFresh R r) hcollision

end KappaLadder
end DWeb
end Erdos599

#print axioms Erdos599.DWeb.KappaLadder.splitGroundedFreshAvoidingStrongSelectedPath_no_hangingCollision
#print axioms Erdos599.DWeb.KappaLadder.SplitGroundedUnusedRecord.stage_unused_reservedControlsFrom
#print axioms Erdos599.DWeb.KappaLadder.splitGroundedFreshAvoidingReservedStrongSelectedPath_no_hangingCollision
#print axioms Erdos599.DWeb.KappaLadder.splitGroundedFreshAvoidingReservedBackwardOwner_rootPrefix
