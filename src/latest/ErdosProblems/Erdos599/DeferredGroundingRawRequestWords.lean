/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.DeferredGroundingRawRootedHindrance

/-!
# Exact signed words for all actual deferred raw transactions

Old requests keep the whole attached word. Edge requests omit only the
final backward gadget. Every backward step is a genuine reference edge
outside the cut and is witnessed on the original selected auxiliary path.
-/

noncomputable section

namespace Erdos599.DWeb.KappaLadder.Deferred

open Set _root_.Erdos599.DirectedPath Alternating
open PopularAuxiliary.Input PopularGroundingBridge GroundingSimultaneousDecode
open GroundingRawSelectedEdgeSwitch

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}
variable {L : Gamma.KappaLadder kappa} {hL : IsKappaHindrance L}
variable {S : Popular.PopularSeparator (popularAuxiliaryIndexed L hL)}

local notation "J" => popularAuxiliaryInput L hL.legal
local notation "U" => popularAuxiliaryIndexed L hL
local notation "K" => reservedGroundedCarrierControls L hL S

def reservedRawRequestSteps : Request J S.cut → List (SignedEdge V)
  | .inl z => (reservedRawOwnerAttachment (.inl z)).steps
  | .inr e => (reservedRawOwnerAttachment (.inr e)).entrySteps e.1.1 e.1.2
      (strongSelectedPath_finish U S K (.inr e))

def reservedRawRequestBackwardEdges (r : Request J S.cut) : Set (V × V) :=
  directedSignedEdgeSet .backward (reservedRawRequestSteps r)

theorem reservedRawRequestSteps_forwardEdges (r : Request J S.cut) :
    directedSignedEdgeSet .forward (reservedRawRequestSteps r) =
      (reservedRawOwnerAttachment r).forwardEdges := by
  cases r with
  | inl z => exact (reservedRawOwnerAttachment (.inl z)).steps_forwardEdges
  | inr e =>
      exact (reservedRawOwnerAttachment (.inr e)).entrySteps_forwardEdges
        ((strongSelectedWarp U S K).starts_in_source ⟨.inr e, rfl⟩) e.1.1 e.1.2
        (strongSelectedPath_finish U S K (.inr e))

theorem reservedRawRequestSteps_runs (r : Request J S.cut) :
    RunsFromTo (reservedRawOwnerAttachment r).anchor (requestVertex r)
      (reservedRawRequestSteps r) := by
  cases r with
  | inl z =>
      apply (reservedRawOwnerAttachment (.inl z)).steps_runs
      rw [strongSelectedPath_finish]
      rfl
  | inr e =>
      exact (reservedRawOwnerAttachment (.inr e)).entrySteps_runs
        ((strongSelectedWarp U S K).starts_in_source ⟨.inr e, rfl⟩) e.1.1 e.1.2
        (strongSelectedPath_finish U S K (.inr e))

theorem reservedRawRequestSteps_nodup (r : Request J S.cut) :
    (reservedRawRequestSteps r).Nodup := by
  have hboundary := popularAuxiliary_hasBoundaryIncidence L hL.legal
  cases r with
  | inl z =>
      exact (reservedRawOwnerAttachment (.inl z)).steps_nodup hboundary
        (reservedStrongSelectedStartingRecord (.inl z)).record_mem_ladder
        ((strongSelectedWarp U S K).starts_in_source ⟨.inl z, rfl⟩)
  | inr e =>
      exact (reservedRawOwnerAttachment (.inr e)).entrySteps_nodup hboundary
        (reservedStrongSelectedStartingRecord (.inr e)).record_mem_ladder
        ((strongSelectedWarp U S K).starts_in_source ⟨.inr e, rfl⟩) e.1.1 e.1.2
        (strongSelectedPath_finish U S K (.inr e))

theorem reservedRawRequestBackward_subset_tail (r : Request J S.cut) :
    reservedRawRequestBackwardEdges r ⊆
      (J).representedEdges (reservedRawOwnerAttachment r).tail := by
  cases r with
  | inl z =>
      change directedSignedEdgeSet .backward (reservedRawOwnerAttachment (.inl z)).steps ⊆ _
      rw [(reservedRawOwnerAttachment (.inl z)).steps_backwardEdges
        ((strongSelectedWarp U S K).starts_in_source ⟨.inl z, rfl⟩)]
  | inr e =>
      rw [(reservedRawOwnerAttachment (.inr e)).entrySteps_backward_partition
        ((strongSelectedWarp U S K).starts_in_source ⟨.inr e, rfl⟩) e.1.1 e.1.2
        (strongSelectedPath_finish U S K (.inr e))]
      exact Set.subset_union_left

/-- Every actually used backward step survives the auxiliary cut deletion. -/
theorem reservedRawRequestBackward_subset_cut_reference (r : Request J S.cut) :
    reservedRawRequestBackwardEdges r ⊆
      (((J).familyEdges \ (reservedStrongSelectedStartingRecord r).record.edgeSet) \
        GroundingCut.CE J S.cut) := by
  cases r with
  | inl z =>
      intro e he
      have hrep := reservedRawRequestBackward_subset_tail (.inl z) he
      exact ⟨(reservedRawOwnerAttachment (.inl z)).backward_subset_ownerDeleted
          (reservedStrongSelectedStartingRecord (.inl z)).record_mem_ladder hrep,
        fun heC ↦ reservedRawOwnerOldRequest_no_cut_gadget z e heC
          ((reservedRawOwnerAttachment (.inl z)).tail_support_subset hrep.1)⟩
  | inr e =>
      exact (reservedRawOwnerAttachment (.inr e)).entrySteps_backward_subset_cut_reference
        (popularAuxiliary_hasBoundaryIncidence L hL.legal)
        (reservedStrongSelectedStartingRecord (.inr e)).record_mem_ladder
        ((strongSelectedWarp U S K).starts_in_source ⟨.inr e, rfl⟩) e.1.1 e.1.2
        (strongSelectedPath_finish U S K (.inr e)) (GroundingCut.CE J S.cut)
        (selected_edgeCut_gadget_unique U S K e)

theorem reservedRawRequestBackward_gadget (r : Request J S.cut) {e : V × V}
    (he : e ∈ reservedRawRequestBackwardEdges r) :
    LambdaVertex.edge e.1 e.2 ∈ (strongSelectedPath U S K r).support ∧
      LambdaVertex.edge e.1 e.2 ∉ S.cut := by
  have hrep := reservedRawRequestBackward_subset_tail r he
  have href := reservedRawRequestBackward_subset_cut_reference r he
  exact ⟨(reservedRawOwnerAttachment r).tail_support_subset hrep.1,
    fun heC ↦ href.2 ⟨heC, hrep.2⟩⟩

#print axioms reservedRawRequestSteps_runs
#print axioms reservedRawRequestBackward_subset_cut_reference
#print axioms reservedRawRequestBackward_gadget

end Erdos599.DWeb.KappaLadder.Deferred
