/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SplitGroundingGroundedFreshRelevantForwardAnchorNormalization
import ErdosProblems.Erdos599.SplitGroundingGroundedRelevantControlResolution

/-!
# Native-frontier normalization of stopped controls

An unrooted represented-cut control is not a terminal obstruction.  Active
and retained controls expose either a concrete prefix stopped at the actual
frontier or an unrooted selected-route anchor.  Inactive controls expose a
finite ladder segment whose retained contact is rooted.  This file feeds all
anchor and inactive-segment alternatives into the existing native-frontier
backward normalizer while preserving the original control resolution.
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

private abbrev ControlNormInput :=
  L.splitGroundedPopularAuxiliaryInput hL.legal

private abbrev ControlNormIndexed :=
  L.splitGroundedPopularAuxiliaryIndexed hL hground

private abbrev ControlNormControls :=
  L.splitGroundedFreshAvoidingCanonicalControls hL hground hnotFresh S

private abbrev ControlNormRecord :=
  L.splitGroundedFreshAvoidingCanonicalUnusedRecord
    hL hground hnotFresh S

private abbrev ControlNormFrontier : Set V :=
  L.splitGroundedRelevantSourceFirstBB hL.legal S.cut

private abbrev ControlNormEdges : Set (V × V) :=
  erasedSelectedSwitchedEdgesAt
    (ControlNormIndexed (L := L) (hL := hL) (hground := hground)) S
    (ControlNormControls (L := L) (hL := hL)
      (hground := hground) (hnotFresh := hnotFresh) (S := S))
    (ControlNormFrontier (L := L) (hL := hL) (S := S))

private abbrev ControlNormSources : Set V :=
  Gamma.source \ {
    (ControlNormRecord (L := L) (hL := hL) (hground := hground)
      (hnotFresh := hnotFresh) (S := S)).record.initial}

/-- Normalize an unrooted selected trace initial without requiring a
forward-splice wrapper. -/
theorem exists_splitGroundedFreshRelevant_initialAnchorNormalization
    (owner : ActiveControlRequestAt
      (ControlNormIndexed (L := L) (hL := hL) (hground := hground)) S
      (ControlNormControls (L := L) (hL := hL)
        (hground := hground) (hnotFresh := hnotFresh) (S := S))
      (ControlNormFrontier (L := L) (hL := hL) (S := S)))
    (hnot : ¬ ∃ a ∈ ControlNormSources
        (L := L) (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S),
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ ControlNormEdges
          (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S)) a
        (selectedRequestTrace
          (ControlNormIndexed (L := L) (hL := hL) (hground := hground)) S
          (ControlNormControls (L := L) (hL := hL)
            (hground := hground) (hnotFresh := hnotFresh) (S := S))
          (chosenRequest owner.1)).initial) :
    ∃ state : L.SplitGroundedFreshRelevantBackwardState
        (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S),
      state.control = owner ∧
        L.SplitGroundedFreshRelevantBackwardNormalizationResult state := by
  let R := ControlNormRecord (L := L) (hL := hL)
    (hground := hground) (hnotFresh := hnotFresh) (S := S)
  obtain ⟨parent, q, hparent, hqStart, hqFinish, hqSupport, hqEdges⟩ :=
    R.exists_selectedRequest_allowedRootPrefix (chosenRequest owner.1)
  have hqNot : ¬ ∃ a ∈ ControlNormSources
      (L := L) (hL := hL) (hground := hground)
      (hnotFresh := hnotFresh) (S := S),
    Relation.ReflTransGen
      (fun x y ↦ (x, y) ∈ ControlNormEdges
        (L := L) (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S)) a q.finish := by
    simpa only [hqFinish] using hnot
  have hpStart : (strongSelectedPath
      (ControlNormIndexed (L := L) (hL := hL) (hground := hground)) S
      (ControlNormControls (L := L) (hL := hL)
        (hground := hground) (hnotFresh := hnotFresh) (S := S))
      (chosenRequest owner.1)).start ∈
      (ControlNormInput (L := L) (hL := hL)).lambda.source :=
    (strongSelectedWarp
      (ControlNormIndexed (L := L) (hL := hL) (hground := hground)) S
      (ControlNormControls (L := L) (hL := hL)
        (hground := hground) (hnotFresh := hnotFresh) (S := S)))
      |>.starts_in_source ⟨chosenRequest owner.1, rfl⟩
  have hinitialCarrier : (selectedRequestTrace
      (ControlNormIndexed (L := L) (hL := hL) (hground := hground)) S
      (ControlNormControls (L := L) (hL := hL)
        (hground := hground) (hnotFresh := hnotFresh) (S := S))
      (chosenRequest owner.1)).initial ∈
      (ControlNormInput (L := L) (hL := hL)).decodedVertexCarrier
        (strongSelectedPath
          (ControlNormIndexed (L := L) (hL := hL)
            (hground := hground)) S
          (ControlNormControls (L := L) (hL := hL)
            (hground := hground) (hnotFresh := hnotFresh) (S := S))
          (chosenRequest owner.1)) := by
    apply GroundingErasedCarrierRank.selectedErasedCompression_vertexSet_subset_decodedVertexCarrier
      (ControlNormIndexed (L := L) (hL := hL) (hground := hground)) S
      (ControlNormControls (L := L) (hL := hL)
        (hground := hground) (hnotFresh := hnotFresh) (S := S))
      (chosenRequest owner.1)
    exact Set.mem_of_eq_of_mem
      (selectedErasedCompression
        (ControlNormIndexed (L := L) (hL := hL) (hground := hground)) S
        (ControlNormControls (L := L) (hL := hL)
          (hground := hground) (hnotFresh := hnotFresh) (S := S))
        (chosenRequest owner.1)).initial_eq.symm
      (selectedErasedCompression
        (ControlNormIndexed (L := L) (hL := hL) (hground := hground)) S
        (ControlNormControls (L := L) (hL := hL)
          (hground := hground) (hnotFresh := hnotFresh) (S := S))
        (chosenRequest owner.1)).path.initial_mem_vertexSet
  have hinitialParent : (selectedRequestTrace
      (ControlNormIndexed (L := L) (hL := hL) (hground := hground)) S
      (ControlNormControls (L := L) (hL := hL)
        (hground := hground) (hnotFresh := hnotFresh) (S := S))
      (chosenRequest owner.1)).initial ∈ parent.support := by
    rw [← hqFinish]
    exact hqSupport q.finish_mem_support
  have hexposed : parent ∈ exposedLadderPaths
      (ControlNormInput (L := L) (hL := hL))
      (strongSelectedPath
        (ControlNormIndexed (L := L) (hL := hL) (hground := hground)) S
        (ControlNormControls (L := L) (hL := hL)
          (hground := hground) (hnotFresh := hnotFresh) (S := S))
        (chosenRequest owner.1)) :=
    (ControlNormInput (L := L) (hL := hL))
      |>.mem_exposedLadderPaths_of_mem_decodedVertexCarrier_of_mem_support
        (L.splitGroundedPopularAuxiliary_proxyPathsFaithful hL)
        _ hpStart hparent.1 hinitialCarrier hinitialParent
  obtain ⟨state, hcontrol, _hparent, hresult⟩ :=
    L.exists_splitGroundedFreshRelevant_anchorBackwardNormalization
      (hL := hL) (hground := hground) (hnotFresh := hnotFresh) (S := S)
      owner parent hparent.1 hexposed q hqStart hqSupport hqEdges hqNot
  exact ⟨state, hcontrol, hresult⟩

/-- Normalize the unrooted start of a concrete selected backward link. -/
theorem exists_splitGroundedFreshRelevant_backwardAnchorNormalization
    (owner : ActiveControlRequestAt
      (ControlNormIndexed (L := L) (hL := hL) (hground := hground)) S
      (ControlNormControls (L := L) (hL := hL)
        (hground := hground) (hnotFresh := hnotFresh) (S := S))
      (ControlNormFrontier (L := L) (hL := hL) (S := S)))
    (link : Link Gamma.graph) (parent : Gamma.DPath)
    (hlink : link ∈ (selectedErasedCompression
      (ControlNormIndexed (L := L) (hL := hL) (hground := hground)) S
      (ControlNormControls (L := L) (hL := hL)
        (hground := hground) (hnotFresh := hnotFresh) (S := S))
      (chosenRequest owner.1)).path.links)
    (hdir : link.direction = .backward)
    (hparent : parent ∈ (ControlNormInput (L := L) (hL := hL)).ladder.paths)
    (hsub : link.path.IsSubpathOf parent)
    (hnot : ¬ ∃ a ∈ ControlNormSources
        (L := L) (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S),
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ ControlNormEdges
          (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S)) a link.path.start) :
    ∃ state : L.SplitGroundedFreshRelevantBackwardState
        (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S),
      state.control = owner ∧
        L.SplitGroundedFreshRelevantBackwardNormalizationResult state := by
  have hparentLimit : parent ∈ L.limitWarp := by
    simpa only [ControlNormInput, splitGroundedPopularAuxiliaryInput,
      limitWarp] using hparent
  obtain ⟨q, hqStart, hqFinish, hqSupport, hqEdges⟩ :=
    L.splitGroundedFreshAvoidingCanonicalBackwardOwner_rootPrefix
      hL hground hnotFresh S (chosenRequest owner.1)
      link hlink hdir parent hparentLimit hsub
  have hqNot : ¬ ∃ a ∈ ControlNormSources
      (L := L) (hL := hL) (hground := hground)
      (hnotFresh := hnotFresh) (S := S),
    Relation.ReflTransGen
      (fun x y ↦ (x, y) ∈ ControlNormEdges
        (L := L) (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S)) a q.finish := by
    simpa only [hqFinish] using hnot
  have hexposed : parent ∈ exposedLadderPaths
      (ControlNormInput (L := L) (hL := hL))
      (strongSelectedPath
        (ControlNormIndexed (L := L) (hL := hL) (hground := hground)) S
        (ControlNormControls (L := L) (hL := hL)
          (hground := hground) (hnotFresh := hnotFresh) (S := S))
        (chosenRequest owner.1)) :=
    L.splitGroundedBackwardLink_parent_exposedAt
      (ControlNormFrontier (L := L) (hL := hL) (S := S))
      owner link hlink hdir parent hparent hsub
  obtain ⟨state, hcontrol, _hparent, hresult⟩ :=
    L.exists_splitGroundedFreshRelevant_anchorBackwardNormalization
      (hL := hL) (hground := hground) (hnotFresh := hnotFresh) (S := S)
      owner parent hparentLimit hexposed q hqStart hqSupport hqEdges hqNot
  exact ⟨state, hcontrol, hresult⟩

/-- Complete normalization of a stopped-control resolution.  A stopped
active prefix is retained with its original control equality; every other
constructor produces an actual native-frontier backward-normalization
state, while keeping the precise origin constructor as data. -/
inductive SplitGroundedFreshRelevantControlNormalizationAt
    (c : ControlRequest (ControlNormInput (L := L) (hL := hL)) S.cut) : Prop
  | stopped
      (owner : ActiveControlRequestAt
        (ControlNormIndexed (L := L) (hL := hL) (hground := hground)) S
        (ControlNormControls (L := L) (hL := hL)
          (hground := hground) (hnotFresh := hnotFresh) (S := S))
        (ControlNormFrontier (L := L) (hL := hL) (S := S)))
      (control_eq : owner.1 = c)
      (control_not_rooted : ¬ ∃ a ∈ ControlNormSources
          (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S),
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ ControlNormEdges
            (L := L) (hL := hL) (hground := hground)
            (hnotFresh := hnotFresh) (S := S)) a c.1)
      (data : ActiveControlAtStoppedPrefix
        (ControlNormIndexed (L := L) (hL := hL) (hground := hground)) S
        (ControlNormControls (L := L) (hL := hL)
          (hground := hground) (hnotFresh := hnotFresh) (S := S))
        (ControlNormFrontier (L := L) (hL := hL) (S := S))
        (ControlNormSources (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S)) owner)
  | activeNormalized
      (owner : ActiveControlRequestAt
        (ControlNormIndexed (L := L) (hL := hL) (hground := hground)) S
        (ControlNormControls (L := L) (hL := hL)
          (hground := hground) (hnotFresh := hnotFresh) (S := S))
        (ControlNormFrontier (L := L) (hL := hL) (S := S)))
      (control_eq : owner.1 = c)
      (control_not_rooted : ¬ ∃ a ∈ ControlNormSources
          (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S),
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ ControlNormEdges
            (L := L) (hL := hL) (hground := hground)
            (hnotFresh := hnotFresh) (S := S)) a c.1)
      (state : L.SplitGroundedFreshRelevantBackwardState
        (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S))
      (state_control : state.control = owner)
      (result : L.SplitGroundedFreshRelevantBackwardNormalizationResult state)
  | retainedNormalized
      (owner : ActiveControlRequestAt
        (ControlNormIndexed (L := L) (hL := hL) (hground := hground)) S
        (ControlNormControls (L := L) (hL := hL)
          (hground := hground) (hnotFresh := hnotFresh) (S := S))
        (ControlNormFrontier (L := L) (hL := hL) (S := S)))
      (vertex : V)
      (vertex_retained : vertex ∈ retainedForwardVerticesAt
        (ControlNormFrontier (L := L) (hL := hL) (S := S))
        (selectedErasedCompression
          (ControlNormIndexed (L := L) (hL := hL) (hground := hground)) S
          (ControlNormControls (L := L) (hL := hL)
            (hground := hground) (hnotFresh := hnotFresh) (S := S))
          (chosenRequest owner.1)).path)
      (vertex_not_rooted : ¬ ∃ a ∈ ControlNormSources
          (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S),
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ ControlNormEdges
            (L := L) (hL := hL) (hground := hground)
            (hnotFresh := hnotFresh) (S := S)) a vertex)
      (control_not_rooted : ¬ ∃ a ∈ ControlNormSources
          (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S),
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ ControlNormEdges
            (L := L) (hL := hL) (hground := hground)
            (hnotFresh := hnotFresh) (S := S)) a c.1)
      (state : L.SplitGroundedFreshRelevantBackwardState
        (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S))
      (state_control : state.control = owner)
      (result : L.SplitGroundedFreshRelevantBackwardNormalizationResult state)
  | inactiveNormalized
      (data : InactiveStoppedRootObstructionDataAt S
        (ControlNormControls (L := L) (hL := hL)
          (hground := hground) (hnotFresh := hnotFresh) (S := S))
        (ControlNormFrontier (L := L) (hL := hL) (S := S))
        (ControlNormSources (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S)) c)
      (state : L.SplitGroundedFreshRelevantBackwardState
        (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S))
      (state_control : state.control = data.absorber)
      (state_parent : state.parent = data.parent)
      (result : L.SplitGroundedFreshRelevantBackwardNormalizationResult state)

private theorem InactiveStoppedRootObstructionDataAt.support_subset_parent
    (c : ControlRequest (ControlNormInput (L := L) (hL := hL)) S.cut)
    (data : InactiveStoppedRootObstructionDataAt S
      (ControlNormControls (L := L) (hL := hL)
        (hground := hground) (hnotFresh := hnotFresh) (S := S))
      (ControlNormFrontier (L := L) (hL := hL) (S := S))
      (ControlNormSources (L := L) (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S)) c) :
    data.segment.support ⊆ data.parent.support := by
  intro x hx
  by_cases hxFinish : x = data.segment.finish
  · rw [hxFinish, data.segment_finish]
    rcases data.contact_before_control with
      ⟨_m, _n, _hcontact, hcontrol, _hmn⟩
    exact GroundingCut.occursAt_mem_support hcontrol
  · obtain ⟨y, hxy⟩ :=
      data.segment.walk.exists_outgoing_edge_of_mem_of_ne_finish hx hxFinish
    exact (data.parent.edgeSet_subset_support_prod
      (data.segment_edges hxy)).1

/-- Normalize an exact stopped-control resolution at the canonical relevant
frontier. -/
theorem SplitGroundedRelevantControlResolutionAt.normalizeFreshRelevant
    (c : ControlRequest (ControlNormInput (L := L) (hL := hL)) S.cut)
    (resolution : SplitGroundedRelevantControlResolutionAt
      (ControlNormRecord (L := L) (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S))
      (ControlNormFrontier (L := L) (hL := hL) (S := S)) c) :
    L.SplitGroundedFreshRelevantControlNormalizationAt
      (hL := hL) (hground := hground)
      (hnotFresh := hnotFresh) (S := S) c := by
  cases resolution with
  | active owner heq hnotControl outcome =>
      cases outcome with
      | stopped data => exact .stopped owner heq hnotControl data
      | initial hnot =>
          obtain ⟨state, hcontrol, hresult⟩ :=
            L.exists_splitGroundedFreshRelevant_initialAnchorNormalization
              (hL := hL) (hground := hground)
              (hnotFresh := hnotFresh) (S := S) owner hnot
          exact .activeNormalized owner heq hnotControl state hcontrol hresult
      | backwardOwner link parent hlink hdir hparent hsub hnot =>
          obtain ⟨state, hcontrol, hresult⟩ :=
            L.exists_splitGroundedFreshRelevant_backwardAnchorNormalization
              (hL := hL) (hground := hground)
              (hnotFresh := hnotFresh) (S := S)
              owner link parent hlink hdir hparent hsub hnot
          exact .activeNormalized owner heq hnotControl state hcontrol hresult
  | retained owner vertex hvertex hvertexNot hcontrolNot outcome =>
      cases outcome with
      | initial hnot =>
          obtain ⟨state, hcontrol, hresult⟩ :=
            L.exists_splitGroundedFreshRelevant_initialAnchorNormalization
              (hL := hL) (hground := hground)
              (hnotFresh := hnotFresh) (S := S) owner hnot
          exact .retainedNormalized owner vertex hvertex hvertexNot hcontrolNot
            state hcontrol hresult
      | backwardOwner link parent hlink hdir hparent hsub hnot =>
          obtain ⟨state, hcontrol, hresult⟩ :=
            L.exists_splitGroundedFreshRelevant_backwardAnchorNormalization
              (hL := hL) (hground := hground)
              (hnotFresh := hnotFresh) (S := S)
              owner link parent hlink hdir hparent hsub hnot
          exact .retainedNormalized owner vertex hvertex hvertexNot hcontrolNot
            state hcontrol hresult
  | inactive data hcontrolNot _inactiveResolution =>
      have hparentInput : data.parent ∈
          (ControlNormInput (L := L) (hL := hL)).ladder.paths :=
        GroundingErasedCarrierRank.exposedLadderPaths_subset_ladder
          (L.splitGroundedPopularAuxiliary_proxyPathsFaithful hL)
          _ data.parent_exposed
      have hparentLimit : data.parent ∈ L.limitWarp := by
        simpa only [ControlNormInput, splitGroundedPopularAuxiliaryInput,
          limitWarp] using hparentInput
      have hsupport := data.support_subset_parent c
      have hstart : ∃ a ∈ ControlNormSources
          (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S),
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ ControlNormEdges
            (L := L) (hL := hL) (hground := hground)
            (hnotFresh := hnotFresh) (S := S)) a data.segment.start := by
        simpa only [data.segment_start] using data.contact_rooted
      have hfinish : ¬ ∃ a ∈ ControlNormSources
          (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S),
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ ControlNormEdges
            (L := L) (hL := hL) (hground := hground)
            (hnotFresh := hnotFresh) (S := S)) a data.segment.finish := by
        simpa only [data.segment_finish] using hcontrolNot
      let nativeResolution := L.splitGroundedRelevantDeletedResolutionAt
        (ControlNormFrontier (L := L) (hL := hL) (S := S))
        data.parent hparentInput data.segment hsupport data.segment_edges
        data.deleted
      let state : L.SplitGroundedFreshRelevantBackwardState
          (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S) := {
        control := data.absorber
        parent := data.parent
        parent_mem := hparentLimit
        parent_exposed := data.parent_exposed
        rootPath := data.segment
        rootPath_start_rooted := hstart
        rootPath_finish_not_rooted := hfinish
        rootPath_support := hsupport
        rootPath_edges := data.segment_edges
        deleted := data.deleted
        deleted_head_not_rooted := data.deleted_head_not_rooted
        resolution := nativeResolution }
      exact .inactiveNormalized data state rfl rfl state.normalize

end DWeb.KappaLadder
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.SplitGroundedRelevantControlResolutionAt.normalizeFreshRelevant
