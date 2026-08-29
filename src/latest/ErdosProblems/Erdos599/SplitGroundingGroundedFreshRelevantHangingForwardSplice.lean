/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SplitGroundingGroundedFreshRelevantBackwardNormalization
import ErdosProblems.Erdos599.SplitGroundingGroundedRelevantLastContactHanging
import ErdosProblems.Erdos599.GroundingStoppedControlRootOutcome

/-!
# Hanging-parent resolution of a native-frontier forward splice

For a hanging limiting-ladder parent, fresh avoidance localizes every
segment contact of the selected route to its own request gadget.  The
segment-local final contact is therefore either the selected request exit,
or the tail represented by an edge request.  At the actual stopping
frontier, a rooted contact has the strict splice position before the last
deleted head.  An unrooted exit is exactly a native stopped-control
dependency; the only remaining hanging case is the explicit unrooted
edge-request tail.

The edge-tail alternative is retained intentionally.  The whole-parent
last contact is the exit, but that exit need not lie in the finite segment,
so identifying the segment-local contact with it would be unsound.
-/

noncomputable section

open Cardinal Set

namespace Erdos599

open DirectedPath Alternating PopularGroundingBridge
open GroundingSimultaneousDecode GroundingErasedDecode
open GroundingErasedSwitchRelation PopularAuxiliary.Input

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

namespace DWeb.KappaLadder

variable {L : Gamma.KappaLadder kappa} {hL : L.IsSplitKappaHindrance}
  {hground : Stationary.IsStationaryBelow kappa L.phiGround}
  {hnotFresh : ¬ Stationary.IsStationaryBelow kappa
    L.freshInessentialGroundStages}
  {S : Popular.PopularSeparator
    (L.splitGroundedPopularAuxiliaryIndexed hL hground)}

private abbrev HangingSpliceInput :=
  L.splitGroundedPopularAuxiliaryInput hL.legal

private abbrev HangingSpliceIndexed :=
  L.splitGroundedPopularAuxiliaryIndexed hL hground

private abbrev HangingSpliceControls :=
  L.splitGroundedFreshAvoidingCanonicalControls hL hground hnotFresh S

private abbrev HangingSpliceRecord :=
  L.splitGroundedFreshAvoidingCanonicalUnusedRecord
    hL hground hnotFresh S

private abbrev HangingSpliceFrontier : Set V :=
  L.splitGroundedRelevantSourceFirstBB hL.legal S.cut

private abbrev HangingSpliceEdges : Set (V × V) :=
  erasedSelectedSwitchedEdgesAt
    (HangingSpliceIndexed (L := L) (hL := hL) (hground := hground)) S
    (HangingSpliceControls (L := L) (hL := hL)
      (hground := hground) (hnotFresh := hnotFresh) (S := S))
    (HangingSpliceFrontier (L := L) (hL := hL) (S := S))

private abbrev HangingSpliceSources : Set V :=
  Gamma.source \ {
    (HangingSpliceRecord (L := L) (hL := hL)
      (hground := hground) (hnotFresh := hnotFresh) (S := S)).record.initial}

/-- Honest three-way resolution of a forward splice whose exposed parent is
hanging.  The rooted branch carries both the strict deleted-head order and
the sharper position at or before the actual incoming tail.  The unrooted
exit is expanded immediately as a stopped-control outcome at the same
frontier.  Only the genuine edge-request-tail dependency remains explicit. -/
theorem splitGroundedFreshRelevant_hangingForwardSplice_outcome
    (state : L.SplitGroundedFreshRelevantBackwardState
      (hL := hL) (hground := hground)
      (hnotFresh := hnotFresh) (S := S))
    (splice : SplitGroundedReducedForwardConflictSpliceData
      (L := L) (hL := hL) (hground := hground) (S := S)
      (K := HangingSpliceControls (L := L) (hL := hL)
        (hground := hground) (hnotFresh := hnotFresh) (S := S))
      (HangingSpliceFrontier (L := L) (hL := hL) (S := S))
      state.parent state.rootPath state.deleted)
    (hhang : PopularAuxiliary.IsHangingPath Gamma state.parent) :
    ((∃ a ∈ HangingSpliceSources (L := L) (hL := hL)
          (hground := hground) (hnotFresh := hnotFresh) (S := S),
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ HangingSpliceEdges
            (L := L) (hL := hL) (hground := hground)
              (hnotFresh := hnotFresh) (S := S))
          a splice.segmentLastContact.vertex) ∧
      GroundingCut.Before (.inl state.rootPath : Gamma.DPath)
        splice.segmentLastContact.vertex state.deleted.head ∧
      GroundingCut.BeforeEq (.inl state.rootPath : Gamma.DPath)
        splice.segmentLastContact.vertex splice.incomingTail) ∨
    StoppedControlUnrootedOutcome
      (HangingSpliceIndexed (L := L) (hL := hL) (hground := hground)) S
      (HangingSpliceControls (L := L) (hL := hL)
        (hground := hground) (hnotFresh := hnotFresh) (S := S))
      (HangingSpliceFrontier (L := L) (hL := hL) (S := S))
      (HangingSpliceSources (L := L) (hL := hL)
        (hground := hground) (hnotFresh := hnotFresh) (S := S))
      splice.contact.owner.1 ∨
    (splice.segmentLastContact.vertex ∈
        requestTailSet (chosenRequest splice.contact.owner.1) ∧
      ¬ ∃ a ∈ HangingSpliceSources (L := L) (hL := hL)
          (hground := hground) (hnotFresh := hnotFresh) (S := S),
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ HangingSpliceEdges
            (L := L) (hL := hL) (hground := hground)
              (hnotFresh := hnotFresh) (S := S))
          a splice.segmentLastContact.vertex) := by
  let U := HangingSpliceIndexed (L := L) (hL := hL)
    (hground := hground)
  let K := HangingSpliceControls (L := L) (hL := hL)
    (hground := hground) (hnotFresh := hnotFresh) (S := S)
  let r := chosenRequest splice.contact.owner.1
  let trace := selectedRequestTrace U S K r
  let E := trace.erasedRoute
  have hvalid : ∀ {s : SignedEdge V}, s ∈ E.steps →
      SignedEdge.Valid (Gamma := Gamma) s := by
    intro s hs
    exact trace.valid s (E.steps_sublist.subset hs)
  have hxRoute : splice.segmentLastContact.vertex ∈
      (selectedErasedCompression U S K r).path.vertexSet := by
    have hx := E.vertexChain_subset_compressionOfValid_vertexSet hvalid
      splice.segmentLastContact.vertex_mem_chain
    simpa only [E, trace, selectedErasedCompression,
      EndpointTrace.erasedCompression] using hx
  have hparentInput : state.parent ∈
      (HangingSpliceInput (L := L) (hL := hL)).ladder.paths := by
    simpa only [HangingSpliceInput, splitGroundedPopularAuxiliaryInput]
      using state.parent_mem
  have hxParent : splice.segmentLastContact.vertex ∈
      state.parent.support :=
    state.rootPath_support splice.segmentLastContact.vertex_mem
  have hcarrier := L.splitGroundedFreshAvoiding_hangingContact_mem_apexCarrier
    (hL := hL) (hground := hground) (hnotFresh := hnotFresh)
      (S := S) r state.parent hparentInput hhang hxRoute hxParent
  have hclass : splice.segmentLastContact.vertex = requestExit r ∨
      splice.segmentLastContact.vertex ∈ requestTailSet r := by
    rw [gadgetCarrier_requestAuxVertex_eq_exit_union_tail] at hcarrier
    rcases hcarrier with hexit | htail
    · exact Or.inl (Set.mem_singleton_iff.mp hexit)
    · exact Or.inr htail
  by_cases hroot : ∃ a ∈ HangingSpliceSources (L := L) (hL := hL)
      (hground := hground) (hnotFresh := hnotFresh) (S := S),
    Relation.ReflTransGen
      (fun x y ↦ (x, y) ∈ HangingSpliceEdges
        (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S))
      a splice.segmentLastContact.vertex
  · have hbefore := splitGroundedFreshRelevant_forwardSplice_contact_before_head
      state splice hroot
    exact Or.inl ⟨hroot, hbefore,
      splice.segmentLastContact_beforeEq_incomingTail hbefore⟩
  · rcases hclass with hexit | htail
    · apply Or.inr
      apply Or.inl
      have hcontrolNot : ¬ ∃ a ∈ HangingSpliceSources
          (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S),
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ HangingSpliceEdges
            (L := L) (hL := hL) (hground := hground)
              (hnotFresh := hnotFresh) (S := S))
          a splice.contact.owner.1 := by
        intro h
        apply hroot
        simpa only [hexit, r, requestExit_chosenRequest] using h
      exact stoppedControl_unrooted_outcome U S K
        (L.splitGroundedPopularAuxiliary_proxyPathsFaithful hL)
        (HangingSpliceFrontier (L := L) (hL := hL) (S := S))
        (HangingSpliceSources (L := L) (hL := hL)
          (hground := hground) (hnotFresh := hnotFresh) (S := S))
        splice.contact.owner.1 hcontrolNot
    · exact Or.inr (Or.inr ⟨htail, hroot⟩)

end DWeb.KappaLadder
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.splitGroundedFreshRelevant_hangingForwardSplice_outcome
