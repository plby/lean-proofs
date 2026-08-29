/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SplitGroundingGroundedRootProvenance
import ErdosProblems.Erdos599.GroundingActiveRequestRootTransfer
import ErdosProblems.Erdos599.GroundingFiniteSourceRootAt

/-!
# Deleted-head transfer for grounded split selected requests

The grounded split selector has a finite allowed-source prefix for every
request.  If that prefix is changed by the simultaneous switch, its last
deleted edge has exactly the four generic causes: the cut, a backward
selected edge, a forward conflict, or stopping at the boundary.  This file
packages that exact reduction without assuming any of the four geometric
callbacks.
-/

noncomputable section

open Cardinal Set

namespace Erdos599

open DirectedPath PopularGroundingBridge
open GroundingSimultaneousDecode GroundingErasedDecode
open GroundingErasedSwitchRelation GroundingErasedForwardConflict

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

namespace DWeb.KappaLadder

variable {L : Gamma.KappaLadder kappa} {hL : L.IsSplitKappaHindrance}
  {hground : Stationary.IsStationaryBelow kappa L.phiGround}
  {S : Popular.PopularSeparator
    (L.splitGroundedPopularAuxiliaryIndexed hL hground)}
  {K : GroundingSelection.Controls S}

namespace SplitGroundedUnusedRecord

/-- Exact four-case reduction for rooting the initial anchor of a grounded
split selected request after the switch has been stopped at `T`. -/
theorem selectedRequest_initial_rootedAt_of_lastDeletedHead_cases
    (R : L.SplitGroundedUnusedRecord hL hground S K)
    (T : Set V)
    (r : Request (L.splitGroundedPopularAuxiliaryInput hL.legal) S.cut)
    (hCE : ∀ (parent : Gamma.DPath) (q : FinitePath Gamma.graph),
      parent ∈ Gamma.inessentialPaths L.limitWarp →
      q.start ∈ Gamma.source \ {R.record.initial} →
      q.finish = (selectedRequestTrace
        (L.splitGroundedPopularAuxiliaryIndexed hL hground) S K r).initial →
      q.support ⊆ parent.support → q.edgeSet ⊆ parent.edgeSet →
      ∀ (D : LastDeletedHead q (erasedSelectedSwitchedEdgesAt
          (L.splitGroundedPopularAuxiliaryIndexed hL hground) S K T)) u,
        (u, D.head) ∈ q.edgeSet →
        (u, D.head) ∈ GroundingCut.CE
          (L.splitGroundedPopularAuxiliaryInput hL.legal) S.cut →
        ∃ a ∈ Gamma.source \ {R.record.initial},
          Relation.ReflTransGen
            (fun x y ↦ (x, y) ∈ erasedSelectedSwitchedEdgesAt
              (L.splitGroundedPopularAuxiliaryIndexed hL hground) S K T)
            a D.head)
    (hbackward : ∀ (parent : Gamma.DPath) (q : FinitePath Gamma.graph),
      parent ∈ Gamma.inessentialPaths L.limitWarp →
      q.start ∈ Gamma.source \ {R.record.initial} →
      q.finish = (selectedRequestTrace
        (L.splitGroundedPopularAuxiliaryIndexed hL hground) S K r).initial →
      q.support ⊆ parent.support → q.edgeSet ⊆ parent.edgeSet →
      ∀ (D : LastDeletedHead q (erasedSelectedSwitchedEdgesAt
          (L.splitGroundedPopularAuxiliaryIndexed hL hground) S K T)) u,
        (u, D.head) ∈ q.edgeSet →
        (u, D.head) ∈ erasedSelectedDirectionEdgesAt
          (L.splitGroundedPopularAuxiliaryIndexed hL hground) S K T
            .backward →
        ∃ a ∈ Gamma.source \ {R.record.initial},
          Relation.ReflTransGen
            (fun x y ↦ (x, y) ∈ erasedSelectedSwitchedEdgesAt
              (L.splitGroundedPopularAuxiliaryIndexed hL hground) S K T)
            a D.head)
    (hconflict : ∀ (parent : Gamma.DPath) (q : FinitePath Gamma.graph),
      parent ∈ Gamma.inessentialPaths L.limitWarp →
      q.start ∈ Gamma.source \ {R.record.initial} →
      q.finish = (selectedRequestTrace
        (L.splitGroundedPopularAuxiliaryIndexed hL hground) S K r).initial →
      q.support ⊆ parent.support → q.edgeSet ⊆ parent.edgeSet →
      ∀ (D : LastDeletedHead q (erasedSelectedSwitchedEdgesAt
          (L.splitGroundedPopularAuxiliaryIndexed hL hground) S K T)) u,
        (u, D.head) ∈ q.edgeSet →
        (u, D.head) ∈ forwardConflictCutEdgesAt
          (L.splitGroundedPopularAuxiliaryIndexed hL hground) S K T →
        ∃ a ∈ Gamma.source \ {R.record.initial},
          Relation.ReflTransGen
            (fun x y ↦ (x, y) ∈ erasedSelectedSwitchedEdgesAt
              (L.splitGroundedPopularAuxiliaryIndexed hL hground) S K T)
            a D.head)
    (hboundary : ∀ (parent : Gamma.DPath) (q : FinitePath Gamma.graph),
      parent ∈ Gamma.inessentialPaths L.limitWarp →
      q.start ∈ Gamma.source \ {R.record.initial} →
      q.finish = (selectedRequestTrace
        (L.splitGroundedPopularAuxiliaryIndexed hL hground) S K r).initial →
      q.support ⊆ parent.support → q.edgeSet ⊆ parent.edgeSet →
      ∀ (D : LastDeletedHead q (erasedSelectedSwitchedEdgesAt
          (L.splitGroundedPopularAuxiliaryIndexed hL hground) S K T)) u,
        (u, D.head) ∈ q.edgeSet →
        (u, D.head) ∈ residualLadderEdges
          (L.splitGroundedPopularAuxiliaryIndexed hL hground) S → u ∈ T →
        ∃ a ∈ Gamma.source \ {R.record.initial},
          Relation.ReflTransGen
            (fun x y ↦ (x, y) ∈ erasedSelectedSwitchedEdgesAt
              (L.splitGroundedPopularAuxiliaryIndexed hL hground) S K T)
            a D.head) :
    ∃ a ∈ Gamma.source \ {R.record.initial},
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ erasedSelectedSwitchedEdgesAt
          (L.splitGroundedPopularAuxiliaryIndexed hL hground) S K T) a
        (selectedRequestTrace
          (L.splitGroundedPopularAuxiliaryIndexed hL hground) S K r).initial := by
  obtain ⟨parent, q, hparent, hqStart, hqFinish, hqSupport, hqEdges⟩ :=
    R.exists_selectedRequest_allowedRootPrefix r
  have hqFamily : q.edgeSet ⊆
      (L.splitGroundedPopularAuxiliaryInput hL.legal).familyEdges := by
    intro e he
    exact ⟨parent, hparent.1, hqEdges he⟩
  have hstart : ∃ a ∈ Gamma.source \ {R.record.initial},
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ erasedSelectedSwitchedEdgesAt
          (L.splitGroundedPopularAuxiliaryIndexed hL hground) S K T)
        a q.start := ⟨q.start, hqStart, .refl⟩
  obtain ⟨a, ha, hareach⟩ :=
    exists_root_reaching_finishAt_of_lastDeletedHead_cases K T
      (Gamma.source \ {R.record.initial}) q hqFamily hstart
      (hCE parent q hparent hqStart hqFinish hqSupport hqEdges)
      (hbackward parent q hparent hqStart hqFinish hqSupport hqEdges)
      (hconflict parent q hparent hqStart hqFinish hqSupport hqEdges)
      (hboundary parent q hparent hqStart hqFinish hqSupport hqEdges)
  exact ⟨a, ha, hqFinish ▸ hareach⟩

end SplitGroundedUnusedRecord
end DWeb.KappaLadder
end Erdos599

#print axioms Erdos599.DWeb.KappaLadder.SplitGroundedUnusedRecord.selectedRequest_initial_rootedAt_of_lastDeletedHead_cases
