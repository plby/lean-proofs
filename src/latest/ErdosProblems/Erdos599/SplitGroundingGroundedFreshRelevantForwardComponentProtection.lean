/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SplitGroundingGroundedFreshRelevantForwardComponentExchange
import ErdosProblems.Erdos599.SplitGroundingGroundedFreshRelevantExposedIsolationNext

/-!
# Rank protection for a concrete forward component exchange

The exact component exchange cuts an exposed limiting-ladder parent at the
retained forward tail of its selected owner.  The active-control recursion
places every higher-rank apex attachment strictly before that tail.  Hence
every actual displaced-component contact, which lies weakly after the cut,
is strictly after all such attachments.  This is the one-step preservation
invariant used by the simultaneous rank-ordered component construction.
-/

noncomputable section

open Cardinal Set

namespace Erdos599

open DirectedPath Alternating PopularGroundingBridge
open GroundingSimultaneousDecode GroundingErasedDecode

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

namespace DWeb.KappaLadder

variable {L : Gamma.KappaLadder kappa} {hL : L.IsSplitKappaHindrance}
  {hground : Stationary.IsStationaryBelow kappa L.phiGround}
  {hnotFresh : ¬ Stationary.IsStationaryBelow kappa
    L.freshInessentialGroundStages}
  {S : Popular.PopularSeparator
    (L.splitGroundedPopularAuxiliaryIndexed hL hground)}

private abbrev ProtectionIndexed :=
  L.splitGroundedPopularAuxiliaryIndexed hL hground

private abbrev ProtectionControls :=
  L.splitGroundedFreshAvoidingCanonicalControls hL hground hnotFresh S

private abbrev ProtectionFrontier : Set V :=
  L.splitGroundedFreshRelevantStoppingFrontier (hL := hL) (S := S)

/-- Every higher-rank active apex attachment to the exchanged parent lies
strictly before every concrete displaced-component contact returned by the
terminal-update exchange.  In particular, the tail replacement cannot
delete such an attachment. -/
theorem SplitGroundedReducedForwardConflictSpliceData.laterActiveApex_before_displacedContact
    (state : L.SplitGroundedFreshRelevantBackwardState
      (hL := hL) (hground := hground)
      (hnotFresh := hnotFresh) (S := S))
    (splice : SplitGroundedReducedForwardConflictSpliceData
      (L := L) (hL := hL) (hground := hground) (S := S)
      (K := ProtectionControls (L := L) (hL := hL)
        (hground := hground) (hnotFresh := hnotFresh) (S := S))
      (ProtectionFrontier (L := L) (hL := hL) (S := S))
      state.parent state.rootPath state.deleted)
    (owner_eq : splice.contact.owner.1 = state.control.1)
    (same_tail : splice.incomingTail = splice.contact.forwardEdge.1)
    {contact : V}
    (hcontactOrder : GroundingCut.BeforeEq state.parent
      splice.incomingTail contact)
    (d : ActiveControlRequestAt
      (ProtectionIndexed (L := L) (hL := hL) (hground := hground)) S
      (ProtectionControls (L := L) (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S))
      (ProtectionFrontier (L := L) (hL := hL) (S := S)))
    (hrank : controlRank
      (ProtectionIndexed (L := L) (hL := hL) (hground := hground)) S
        splice.contact.owner.1 <
      controlRank
        (ProtectionIndexed (L := L) (hL := hL) (hground := hground)) S
        d.1)
    (hApex : requestAuxVertex (chosenRequest d.1) ∈
      PopularSwitching.ladderTrace
        (L.splitGroundedPopularAuxiliaryInput hL.legal) state.parent) :
    GroundingCut.Before state.parent d.1.1 contact := by
  have howner : state.control = splice.contact.owner :=
    Subtype.ext owner_eq.symm
  have hexposed : state.parent ∈ exposedLadderPaths
      (L.splitGroundedPopularAuxiliaryInput hL.legal)
      (strongSelectedPath
        (ProtectionIndexed (L := L) (hL := hL) (hground := hground)) S
        (ProtectionControls (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S))
        (chosenRequest splice.contact.owner.1)) := by
    simpa only [howner] using state.parent_exposed
  have htailRetained : splice.incomingTail ∈ retainedForwardVerticesAt
      (ProtectionFrontier (L := L) (hL := hL) (S := S))
      (selectedErasedCompression
        (ProtectionIndexed (L := L) (hL := hL) (hground := hground)) S
        (ProtectionControls (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S))
        (chosenRequest splice.contact.owner.1)).path := by
    have htail := (retainedForwardEdgeAt_endpoints
      (ProtectionFrontier (L := L) (hL := hL) (S := S)) _
      splice.contact.retained).1
    simpa only [same_tail] using htail
  have htailParent : splice.incomingTail ∈ state.parent.support := by
    exact state.rootPath_support
      ((state.rootPath.edgeSet_subset_support_prod splice.incoming_mem).1)
  exact L.splitGroundedFreshRelevant_activeLaterApex_before_of_retainedForward_beforeEq
    (hL := hL) (hground := hground) (hnotFresh := hnotFresh) (S := S)
    (ProtectionFrontier (L := L) (hL := hL) (S := S))
    splice.contact.owner d hrank state.parent hexposed hApex
    htailRetained htailParent hcontactOrder

/-- The exchanged suffix is private to its selected owner among all active
controls.  Lower-rank selected routes miss the exposed parent altogether;
higher-rank routes can meet it only in their apex gadget, and activity puts
that entire gadget strictly before the retained forward cut.  This is the
one-step noninterference theorem needed to union the rank-ordered component
exchanges. -/
theorem SplitGroundedReducedForwardConflictSpliceData.otherActiveRoute_no_contact_after_incomingTail
    (state : L.SplitGroundedFreshRelevantBackwardState
      (hL := hL) (hground := hground)
      (hnotFresh := hnotFresh) (S := S))
    (splice : SplitGroundedReducedForwardConflictSpliceData
      (L := L) (hL := hL) (hground := hground) (S := S)
      (K := ProtectionControls (L := L) (hL := hL)
        (hground := hground) (hnotFresh := hnotFresh) (S := S))
      (ProtectionFrontier (L := L) (hL := hL) (S := S))
      state.parent state.rootPath state.deleted)
    (owner_eq : splice.contact.owner.1 = state.control.1)
    (same_tail : splice.incomingTail = splice.contact.forwardEdge.1)
    (d : ActiveControlRequestAt
      (ProtectionIndexed (L := L) (hL := hL) (hground := hground)) S
      (ProtectionControls (L := L) (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S))
      (ProtectionFrontier (L := L) (hL := hL) (S := S)))
    (hne : d.1 ≠ splice.contact.owner.1)
    {z : V}
    (hzRoute : z ∈ (selectedErasedCompression
      (ProtectionIndexed (L := L) (hL := hL) (hground := hground)) S
      (ProtectionControls (L := L) (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S))
      (chosenRequest d.1)).path.vertexSet)
    (hzParent : z ∈ state.parent.support)
    (hafter : GroundingCut.BeforeEq state.parent splice.incomingTail z) :
    False := by
  let U := ProtectionIndexed (L := L) (hL := hL) (hground := hground)
  let K := ProtectionControls (L := L) (hL := hL) (hground := hground)
    (hnotFresh := hnotFresh) (S := S)
  let T := ProtectionFrontier (L := L) (hL := hL) (S := S)
  have howner : state.control = splice.contact.owner :=
    Subtype.ext owner_eq.symm
  have hexposed : state.parent ∈ exposedLadderPaths
      (L.splitGroundedPopularAuxiliaryInput hL.legal)
      (strongSelectedPath U S K
        (chosenRequest splice.contact.owner.1)) := by
    simpa only [howner] using state.parent_exposed
  have htailRetained : splice.incomingTail ∈ retainedForwardVerticesAt T
      (selectedErasedCompression U S K
        (chosenRequest splice.contact.owner.1)).path := by
    have htail := (retainedForwardEdgeAt_endpoints T _
      splice.contact.retained).1
    simpa only [same_tail] using htail
  have htailParent : splice.incomingTail ∈ state.parent.support := by
    exact state.rootPath_support
      ((state.rootPath.edgeSet_subset_support_prod splice.incoming_mem).1)
  rcases lt_trichotomy
      (controlRank U S d.1)
      (controlRank U S splice.contact.owner.1) with hdo | heq | hod
  · have hdecoded : z ∈
        (L.splitGroundedPopularAuxiliaryInput hL.legal).decodedVertexCarrier
          (strongSelectedPath U S K (chosenRequest d.1)) :=
      GroundingErasedCarrierRank.selectedErasedCompression_vertexSet_subset_decodedVertexCarrier
        U S K (chosenRequest d.1) hzRoute
    have hforwardTail : splice.contact.forwardEdge.1 ∈
        state.parent.support := by
      simpa only [← same_tail] using htailParent
    exact Set.disjoint_left.1
      (L.splitGroundedFreshRelevant_earlierRoute_disjoint_forwardExposedParent
        (hL := hL) (hground := hground) (hnotFresh := hnotFresh) (S := S)
        T splice.contact.owner d hdo state.parent hexposed
        splice.contact.retained hforwardTail)
      hdecoded hzParent
  · exact hne ((controlRank U S).injective heq)
  · have hApex :=
      L.splitGroundedFreshRelevant_laterRoute_contact_exposedParent_apexTrace
        (hL := hL) (hground := hground) (hnotFresh := hnotFresh) (S := S)
        T splice.contact.owner d hod state.parent hexposed hzRoute hzParent
    have hzApex :=
      L.splitGroundedFreshRelevant_laterRoute_contact_exposedParent_mem_apexCarrier
        (hL := hL) (hground := hground) (hnotFresh := hnotFresh) (S := S)
        T splice.contact.owner d hod state.parent hexposed hzRoute hzParent
    have hzBeforeTail :=
      L.splitGroundedFreshRelevant_laterApexCarrier_before_retainedForward
        (hL := hL) (hground := hground) (hnotFresh := hnotFresh) (S := S)
        T splice.contact.owner d hod state.parent hexposed hApex hzApex
        htailRetained htailParent
    exact hzBeforeTail.2
      (GroundingCutDecoder.beforeEq_antisymm hzBeforeTail.1 hafter)

/-- An edge of the native stopped switched relation whose head lies on the
exchanged parent weakly after the retained-forward cut is either an actual
surviving residual edge, or belongs to the retained forward part of the
splice owner's own selected route.  No other active selected route can enter
that suffix: its head would be a forbidden post-cut contact from
`otherActiveRoute_no_contact_after_incomingTail`.

This is the selected-entry half of the relation-component protection needed
by the simultaneous component exchange. -/
theorem SplitGroundedReducedForwardConflictSpliceData.switchedEdge_head_after_incomingTail_cases
    (state : L.SplitGroundedFreshRelevantBackwardState
      (hL := hL) (hground := hground)
      (hnotFresh := hnotFresh) (S := S))
    (splice : SplitGroundedReducedForwardConflictSpliceData
      (L := L) (hL := hL) (hground := hground) (S := S)
      (K := ProtectionControls (L := L) (hL := hL)
        (hground := hground) (hnotFresh := hnotFresh) (S := S))
      (ProtectionFrontier (L := L) (hL := hL) (S := S))
      state.parent state.rootPath state.deleted)
    (owner_eq : splice.contact.owner.1 = state.control.1)
    (same_tail : splice.incomingTail = splice.contact.forwardEdge.1)
    {u z : V}
    (huz : (u, z) ∈ erasedSelectedSwitchedEdgesAt
      (ProtectionIndexed (L := L) (hL := hL) (hground := hground)) S
      (ProtectionControls (L := L) (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S))
      (ProtectionFrontier (L := L) (hL := hL) (S := S)))
    (hzParent : z ∈ state.parent.support)
    (hafter : GroundingCut.BeforeEq state.parent splice.incomingTail z) :
    (u, z) ∈ residualLadderEdges
        (ProtectionIndexed (L := L) (hL := hL) (hground := hground)) S \
      erasedSelectedToggleEdgesAt
        (ProtectionIndexed (L := L) (hL := hL) (hground := hground)) S
        (ProtectionControls (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S))
        (ProtectionFrontier (L := L) (hL := hL) (S := S)) ∨
      (u, z) ∈ retainedForwardEdgesAt
        (ProtectionFrontier (L := L) (hL := hL) (S := S))
        (selectedErasedCompression
          (ProtectionIndexed (L := L) (hL := hL) (hground := hground)) S
          (ProtectionControls (L := L) (hL := hL) (hground := hground)
            (hnotFresh := hnotFresh) (S := S))
          (chosenRequest splice.contact.owner.1)).path := by
  let U := ProtectionIndexed (L := L) (hL := hL) (hground := hground)
  let K := ProtectionControls (L := L) (hL := hL) (hground := hground)
    (hnotFresh := hnotFresh) (S := S)
  let T := ProtectionFrontier (L := L) (hL := hL) (S := S)
  rw [erasedSelectedSwitchedEdgesAt,
    forward_diff_erasedSelectedForwardCutEdgesAt_eq_retained U S K T] at huz
  rcases huz with hresidual | hforward
  · exact Or.inl hresidual
  · simp only [erasedSelectedRetainedForwardEdgesAt, Set.mem_iUnion] at hforward
    obtain ⟨d, hd⟩ := hforward
    by_cases howner : d.1 = splice.contact.owner.1
    · have hdowner : d = splice.contact.owner := Subtype.ext howner
      subst d
      exact Or.inr hd
    · have hrouteEdge : (u, z) ∈
          (selectedErasedCompression U S K
            (chosenRequest d.1)).path.edgeSet := by
        rw [(selectedErasedCompression U S K
          (chosenRequest d.1)).path.edgeSet_eq_directionEdges_union]
        exact Or.inl
          (retainedForwardEdgesAt_subset_directionEdges T _ hd)
      have hzRoute : z ∈
          (selectedErasedCompression U S K
            (chosenRequest d.1)).path.vertexSet :=
        ((selectedErasedCompression U S K
          (chosenRequest d.1)).path.edgeSet_subset_vertexSet_prod
            hrouteEdge).2
      exact False.elim
        (splice.otherActiveRoute_no_contact_after_incomingTail
          state owner_eq same_tail d howner hzRoute hzParent hafter)

end DWeb.KappaLadder
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.SplitGroundedReducedForwardConflictSpliceData.laterActiveApex_before_displacedContact
#print axioms
  Erdos599.DWeb.KappaLadder.SplitGroundedReducedForwardConflictSpliceData.otherActiveRoute_no_contact_after_incomingTail
#print axioms
  Erdos599.DWeb.KappaLadder.SplitGroundedReducedForwardConflictSpliceData.switchedEdge_head_after_incomingTail_cases
