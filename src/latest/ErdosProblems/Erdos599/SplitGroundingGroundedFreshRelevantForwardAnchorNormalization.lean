/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SplitGroundingGroundedFreshRelevantForwardSpliceDescent
import ErdosProblems.Erdos599.SplitGroundingGroundedRootProvenance

/-!
# Native-frontier normalization of retained-forward anchors

An unrooted retained-forward point exposes either the decoded trace initial
or the ambient start of a selected backward link.  In the grounded canonical
selection both vertices have a finite prefix from an allowed original source.
If the point is unrooted, that prefix has a last deleted head in the actual
relation stopped at the source-first relevant frontier.  This file turns both
anchor alternatives into concrete states of the established well-founded
backward normalizer.
-/

noncomputable section

open Cardinal Set

namespace Erdos599

open DirectedPath Alternating PopularGroundingBridge
open GroundingSimultaneousDecode GroundingErasedDecode
open GroundingErasedSwitchRelation

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

namespace DWeb.KappaLadder

variable {L : Gamma.KappaLadder kappa} {hL : L.IsSplitKappaHindrance}
  {hground : Stationary.IsStationaryBelow kappa L.phiGround}
  {hnotFresh : ¬ Stationary.IsStationaryBelow kappa
    L.freshInessentialGroundStages}
  {S : Popular.PopularSeparator
    (L.splitGroundedPopularAuxiliaryIndexed hL hground)}

private abbrev AnchorNormInput :=
  L.splitGroundedPopularAuxiliaryInput hL.legal

private abbrev AnchorNormIndexed :=
  L.splitGroundedPopularAuxiliaryIndexed hL hground

private abbrev AnchorNormControls :=
  L.splitGroundedFreshAvoidingCanonicalControls hL hground hnotFresh S

private abbrev AnchorNormRecord :=
  L.splitGroundedFreshAvoidingCanonicalUnusedRecord
    hL hground hnotFresh S

private abbrev AnchorNormFrontier : Set V :=
  L.splitGroundedRelevantSourceFirstBB hL.legal S.cut

private abbrev AnchorNormEdges : Set (V × V) :=
  erasedSelectedSwitchedEdgesAt
    (AnchorNormIndexed (L := L) (hL := hL) (hground := hground)) S
    (AnchorNormControls (L := L) (hL := hL)
      (hground := hground) (hnotFresh := hnotFresh) (S := S))
    (AnchorNormFrontier (L := L) (hL := hL) (S := S))

private abbrev AnchorNormSources : Set V :=
  Gamma.source \ {
    (AnchorNormRecord (L := L) (hL := hL) (hground := hground)
      (hnotFresh := hnotFresh) (S := S)).record.initial}

/-- Build and normalize the native-frontier state attached to one concrete
allowed-source prefix on an exposed limiting-ladder component.  This public
form is also the exact entry point for active or retained stopped-control
anchors which are not produced by a forward-splice leaf. -/
theorem exists_splitGroundedFreshRelevant_anchorBackwardNormalization
    (owner : ActiveControlRequestAt
      (AnchorNormIndexed (L := L) (hL := hL) (hground := hground)) S
      (AnchorNormControls (L := L) (hL := hL)
        (hground := hground) (hnotFresh := hnotFresh) (S := S))
      (AnchorNormFrontier (L := L) (hL := hL) (S := S)))
    (parent : Gamma.DPath) (hparent : parent ∈ L.limitWarp)
    (hexposed : parent ∈ exposedLadderPaths
      (AnchorNormInput (L := L) (hL := hL))
      (strongSelectedPath
        (AnchorNormIndexed (L := L) (hL := hL) (hground := hground)) S
        (AnchorNormControls (L := L) (hL := hL)
          (hground := hground) (hnotFresh := hnotFresh) (S := S))
        (chosenRequest owner.1)))
    (q : FinitePath Gamma.graph)
    (hqStart : q.start ∈ AnchorNormSources
      (L := L) (hL := hL) (hground := hground)
      (hnotFresh := hnotFresh) (S := S))
    (hqSupport : q.support ⊆ parent.support)
    (hqEdges : q.edgeSet ⊆ parent.edgeSet)
    (hqNot : ¬ ∃ a ∈ AnchorNormSources
        (L := L) (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S),
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ AnchorNormEdges
          (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S)) a q.finish) :
    ∃ state : L.SplitGroundedFreshRelevantBackwardState
        (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S),
      state.control = owner ∧ state.parent = parent ∧
        L.SplitGroundedFreshRelevantBackwardNormalizationResult state := by
  have hqRoot : ∃ a ∈ AnchorNormSources
      (L := L) (hL := hL) (hground := hground)
      (hnotFresh := hnotFresh) (S := S),
    Relation.ReflTransGen
      (fun x y ↦ (x, y) ∈ AnchorNormEdges
        (L := L) (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S)) a q.start :=
    ⟨q.start, hqStart, .refl⟩
  let R := AnchorNormRecord (L := L) (hL := hL)
    (hground := hground) (hnotFresh := hnotFresh) (S := S)
  obtain ⟨D, hDnot⟩ :=
    R.exists_unrootedLastDeletedHead_sourceFirstTotal
      (AnchorNormFrontier (L := L) (hL := hL) (S := S))
      q hqRoot hqNot
  have hparentInput : parent ∈
      (AnchorNormInput (L := L) (hL := hL)).ladder.paths := by
    simpa only [AnchorNormInput, splitGroundedPopularAuxiliaryInput,
      limitWarp] using hparent
  let resolution := L.splitGroundedRelevantDeletedResolutionAt
    (AnchorNormFrontier (L := L) (hL := hL) (S := S))
    parent hparentInput q hqSupport hqEdges D
  let state : L.SplitGroundedFreshRelevantBackwardState
      (hL := hL) (hground := hground)
      (hnotFresh := hnotFresh) (S := S) := {
    control := owner
    parent := parent
    parent_mem := hparent
    parent_exposed := hexposed
    rootPath := q
    rootPath_start_rooted := hqRoot
    rootPath_finish_not_rooted := hqNot
    rootPath_support := hqSupport
    rootPath_edges := hqEdges
    deleted := D
    deleted_head_not_rooted := hDnot
    resolution := resolution }
  exact ⟨state, rfl, rfl, state.normalize⟩

/-- Every terminal retained-forward anchor is immediately converted into a
concrete native-frontier normalization problem.  The trace-initial case uses
the grounded selected request's own parent; the backward-owner case uses the
literal owner supplied by the alternating decoder. -/
theorem SplitGroundedFreshRelevantBackwardNormalizedOutcome.forwardAnchor_has_backwardNormalization
    (state : L.SplitGroundedFreshRelevantBackwardState
      (hL := hL) (hground := hground)
      (hnotFresh := hnotFresh) (S := S))
    (splice : SplitGroundedReducedForwardConflictSpliceData
      (L := L) (hL := hL) (hground := hground) (S := S)
      (K := AnchorNormControls (L := L) (hL := hL)
        (hground := hground) (hnotFresh := hnotFresh) (S := S))
      (AnchorNormFrontier (L := L) (hL := hL) (S := S))
      state.parent state.rootPath state.deleted)
    (anchor : ActiveRetainedForwardVertexUnrootedOutcome
      (AnchorNormIndexed (L := L) (hL := hL) (hground := hground)) S
      (AnchorNormControls (L := L) (hL := hL)
        (hground := hground) (hnotFresh := hnotFresh) (S := S))
      (AnchorNormFrontier (L := L) (hL := hL) (S := S))
      (AnchorNormSources (L := L) (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S))
      splice.contact.owner) :
    ∃ next : L.SplitGroundedFreshRelevantBackwardState
        (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S),
      next.control = splice.contact.owner ∧
        L.SplitGroundedFreshRelevantBackwardNormalizationResult next := by
  let R := AnchorNormRecord (L := L) (hL := hL)
    (hground := hground) (hnotFresh := hnotFresh) (S := S)
  cases anchor with
  | initial hnot =>
      obtain ⟨parent, q, hparent, hqStart, hqFinish,
        hqSupport, hqEdges⟩ :=
        R.exists_selectedRequest_allowedRootPrefix
          (chosenRequest splice.contact.owner.1)
      have hqNot : ¬ ∃ a ∈ AnchorNormSources
          (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S),
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ AnchorNormEdges
            (L := L) (hL := hL) (hground := hground)
            (hnotFresh := hnotFresh) (S := S)) a q.finish := by
        simpa only [hqFinish] using hnot
      have hpStart : (strongSelectedPath
          (AnchorNormIndexed (L := L) (hL := hL) (hground := hground)) S
          (AnchorNormControls (L := L) (hL := hL)
            (hground := hground) (hnotFresh := hnotFresh) (S := S))
          (chosenRequest splice.contact.owner.1)).start ∈
          (AnchorNormInput (L := L) (hL := hL)).lambda.source :=
        (strongSelectedWarp
          (AnchorNormIndexed (L := L) (hL := hL) (hground := hground)) S
          (AnchorNormControls (L := L) (hL := hL)
            (hground := hground) (hnotFresh := hnotFresh) (S := S)))
          |>.starts_in_source ⟨chosenRequest splice.contact.owner.1, rfl⟩
      have hinitialCarrier : (selectedRequestTrace
          (AnchorNormIndexed (L := L) (hL := hL) (hground := hground)) S
          (AnchorNormControls (L := L) (hL := hL)
            (hground := hground) (hnotFresh := hnotFresh) (S := S))
          (chosenRequest splice.contact.owner.1)).initial ∈
          (AnchorNormInput (L := L) (hL := hL)).decodedVertexCarrier
            (strongSelectedPath
              (AnchorNormIndexed (L := L) (hL := hL)
                (hground := hground)) S
              (AnchorNormControls (L := L) (hL := hL)
                (hground := hground) (hnotFresh := hnotFresh) (S := S))
              (chosenRequest splice.contact.owner.1)) := by
        apply GroundingErasedCarrierRank.selectedErasedCompression_vertexSet_subset_decodedVertexCarrier
          (AnchorNormIndexed (L := L) (hL := hL) (hground := hground)) S
          (AnchorNormControls (L := L) (hL := hL)
            (hground := hground) (hnotFresh := hnotFresh) (S := S))
          (chosenRequest splice.contact.owner.1)
        exact Set.mem_of_eq_of_mem
          (selectedErasedCompression
            (AnchorNormIndexed (L := L) (hL := hL) (hground := hground)) S
            (AnchorNormControls (L := L) (hL := hL)
              (hground := hground) (hnotFresh := hnotFresh) (S := S))
            (chosenRequest splice.contact.owner.1)).initial_eq.symm
          (selectedErasedCompression
            (AnchorNormIndexed (L := L) (hL := hL) (hground := hground)) S
            (AnchorNormControls (L := L) (hL := hL)
              (hground := hground) (hnotFresh := hnotFresh) (S := S))
            (chosenRequest splice.contact.owner.1)).path.initial_mem_vertexSet
      have hinitialParent : (selectedRequestTrace
          (AnchorNormIndexed (L := L) (hL := hL) (hground := hground)) S
          (AnchorNormControls (L := L) (hL := hL)
            (hground := hground) (hnotFresh := hnotFresh) (S := S))
          (chosenRequest splice.contact.owner.1)).initial ∈ parent.support := by
        rw [← hqFinish]
        exact hqSupport q.finish_mem_support
      have hexposed : parent ∈ exposedLadderPaths
          (AnchorNormInput (L := L) (hL := hL))
          (strongSelectedPath
            (AnchorNormIndexed (L := L) (hL := hL) (hground := hground)) S
            (AnchorNormControls (L := L) (hL := hL)
              (hground := hground) (hnotFresh := hnotFresh) (S := S))
            (chosenRequest splice.contact.owner.1)) :=
        (AnchorNormInput (L := L) (hL := hL))
          |>.mem_exposedLadderPaths_of_mem_decodedVertexCarrier_of_mem_support
            (L.splitGroundedPopularAuxiliary_proxyPathsFaithful hL)
            _ hpStart hparent.1 hinitialCarrier hinitialParent
      obtain ⟨next, hcontrol, _hparent, hresult⟩ :=
        exists_splitGroundedFreshRelevant_anchorBackwardNormalization
          (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S)
          splice.contact.owner parent hparent.1 hexposed q hqStart
          hqSupport hqEdges hqNot
      exact ⟨next, hcontrol, hresult⟩
  | backwardOwner link parent hlink hdir hparent hsub hnot =>
      have hparentLimit : parent ∈ L.limitWarp := by
        simpa only [AnchorNormInput, splitGroundedPopularAuxiliaryInput,
          limitWarp] using hparent
      obtain ⟨q, hqStart, hqFinish, hqSupport, hqEdges⟩ :=
        L.splitGroundedFreshAvoidingCanonicalBackwardOwner_rootPrefix
          hL hground hnotFresh S (chosenRequest splice.contact.owner.1)
          link hlink hdir parent hparentLimit hsub
      have hqNot : ¬ ∃ a ∈ AnchorNormSources
          (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S),
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ AnchorNormEdges
            (L := L) (hL := hL) (hground := hground)
            (hnotFresh := hnotFresh) (S := S)) a q.finish := by
        simpa only [hqFinish] using hnot
      have hexposed : parent ∈ exposedLadderPaths
          (AnchorNormInput (L := L) (hL := hL))
          (strongSelectedPath
            (AnchorNormIndexed (L := L) (hL := hL) (hground := hground)) S
            (AnchorNormControls (L := L) (hL := hL)
              (hground := hground) (hnotFresh := hnotFresh) (S := S))
            (chosenRequest splice.contact.owner.1)) :=
        L.splitGroundedBackwardLink_parent_exposedAt
          (AnchorNormFrontier (L := L) (hL := hL) (S := S))
          splice.contact.owner link hlink hdir parent hparent hsub
      obtain ⟨next, hcontrol, _hparent, hresult⟩ :=
        exists_splitGroundedFreshRelevant_anchorBackwardNormalization
          (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S)
          splice.contact.owner parent hparentLimit hexposed q hqStart
          hqSupport hqEdges hqNot
      exact ⟨next, hcontrol, hresult⟩

end DWeb.KappaLadder
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.SplitGroundedFreshRelevantBackwardNormalizedOutcome.forwardAnchor_has_backwardNormalization
