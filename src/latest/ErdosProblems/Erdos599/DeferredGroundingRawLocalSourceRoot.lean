/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.DeferredGroundingRawActivePrefixes

/-!
# Actual local source rooting before separator stopping

Switch only the cut-free source-prefix reference of a request, then restore
its genuine starting prefix. The exact signed balance makes the request a
nonisolated sink and puts all positive boundary vertices in the source.
Finite-perturbation rooting handles cycles without rooting their vertices.
The final result is explicitly in the unstopped simultaneous relation.
-/

noncomputable section

namespace Erdos599.DWeb.KappaLadder.Deferred

open Cardinal Order Set _root_.Erdos599.DirectedPath Alternating Ladder
open PopularAuxiliary.Input PopularGroundingBridge GroundingSimultaneousDecode
open Alternating.TerminalContactSwitch

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}
variable {L : Gamma.KappaLadder kappa} {hL : IsKappaHindrance L}
variable {S : Popular.PopularSeparator (popularAuxiliaryIndexed L hL)}

local notation "J" => popularAuxiliaryInput L hL.legal
local notation "EG" => reservedRawSimultaneousEdges (L := L) (hL := hL) (S := S)

def reservedRawLocalSwitchEdges (r : Request J S.cut) : Set (V × V) :=
  (reservedRawActiveReferenceEdges r \ reservedRawRequestBackwardEdges r) ∪
    (reservedRawOwnerAttachment r).forwardEdges

def reservedRawLocalSourceEdges (r : Request J S.cut) : Set (V × V) :=
  reservedRawLocalSwitchEdges r ∪ (reservedRawOwnerAttachment r).sourcePrefix.edgeSet

theorem reservedRawLocalSwitch_subset_simultaneous (r : Request J S.cut) :
    reservedRawLocalSwitchEdges r ⊆ EG := by
  intro e he
  rcases he with he | he
  · exact Or.inl (reservedRawActiveReference_retained r he)
  · exact reservedRawSimultaneousEdges_contains_forward r he

theorem reservedRawLocalSource_subset_simultaneous (r : Request J S.cut) :
    reservedRawLocalSourceEdges r ⊆ EG := by
  intro e he
  rcases he with he | he
  · exact reservedRawLocalSwitch_subset_simultaneous r he
  · exact reservedRawSimultaneousEdges_contains_prefix r he

theorem reservedRawLocalSwitch_biUnique (r : Request J S.cut) :
    Relator.BiUnique (fun x y ↦ (x, y) ∈ reservedRawLocalSwitchEdges r) :=
  ⟨fun _ _ _ he hf ↦ reservedRawSimultaneousEdges_biUnique.1
      (reservedRawLocalSwitch_subset_simultaneous r he)
      (reservedRawLocalSwitch_subset_simultaneous r hf),
    fun _ _ _ he hf ↦ reservedRawSimultaneousEdges_biUnique.2
      (reservedRawLocalSwitch_subset_simultaneous r he)
      (reservedRawLocalSwitch_subset_simultaneous r hf)⟩

theorem reservedRawLocalSource_biUnique (r : Request J S.cut) :
    Relator.BiUnique (fun x y ↦ (x, y) ∈ reservedRawLocalSourceEdges r) :=
  ⟨fun _ _ _ he hf ↦ reservedRawSimultaneousEdges_biUnique.1
      (reservedRawLocalSource_subset_simultaneous r he)
      (reservedRawLocalSource_subset_simultaneous r hf),
    fun _ _ _ he hf ↦ reservedRawSimultaneousEdges_biUnique.2
      (reservedRawLocalSource_subset_simultaneous r he)
      (reservedRawLocalSource_subset_simultaneous r hf)⟩

/-- Exact source-minus-request balance of the actual finite signed word. -/
theorem reservedRawRequest_direction_balance (r : Request J S.cut) (x : V) :
    edgeBalance (reservedRawOwnerAttachment r).forwardEdges x -
      edgeBalance (reservedRawRequestBackwardEdges r) x =
        propInt (x = (reservedRawOwnerAttachment r).anchor) - propInt (x = requestVertex r) := by
  have hF : Relator.BiUnique (fun a b ↦
      (a, b) ∈ directedSignedEdgeSet .forward (reservedRawRequestSteps r)) := by
    rw [reservedRawRequestSteps_forwardEdges]
    exact (reservedRawOwnerAttachment r).forwardEdges_biUnique
      (popularAuxiliary_hasBoundaryIncidence L hL.legal)
      (reservedStrongSelectedStartingRecord r).record_mem_ladder
  have hB : Relator.BiUnique (fun a b ↦ (a, b) ∈ reservedRawRequestBackwardEdges r) :=
    ⟨fun _ _ _ he hf ↦ (J).raw_familyEdges_biUnique.1
        (reservedRawRequestBackward_subset_cut_reference r he).1.1
        (reservedRawRequestBackward_subset_cut_reference r hf).1.1,
      fun _ _ _ he hf ↦ (J).raw_familyEdges_biUnique.2
        (reservedRawRequestBackward_subset_cut_reference r he).1.1
        (reservedRawRequestBackward_subset_cut_reference r hf).1.1⟩
  simpa only [reservedRawRequestSteps_forwardEdges, reservedRawRequestBackwardEdges] using
    (reservedRawRequestSteps_runs r).edgeBalance_forward_sub_backward
      (reservedRawRequestSteps_nodup r) hF hB x

theorem reservedRawLocalSwitch_disjoint_prefix (r : Request J S.cut) :
    Disjoint (reservedRawLocalSwitchEdges r)
      (reservedRawOwnerAttachment r).sourcePrefix.edgeSet := by
  apply Set.disjoint_left.2
  intro e he hp
  rcases he with he | he
  · exact Set.disjoint_left.1 (reservedRawActiveReference_disjoint_prefix r) he.1 hp
  · exact Set.disjoint_left.1
      ((reservedRawOwnerAttachment r).forwardEdges_disjoint_reference
        (popularAuxiliary_hasBoundaryIncidence L hL.legal)
        (reservedStrongSelectedStartingRecord r).record_mem_ladder) he
      ⟨(reservedStrongSelectedStartingRecord r).record,
        (reservedStrongSelectedStartingRecord r).record_mem_ladder,
        (reservedRawOwnerAttachment r).sourcePrefix_edges hp⟩

theorem reservedRawLocalSource_balance (r : Request J S.cut)
    (hB : reservedRawRequestBackwardEdges r ⊆ reservedRawActiveReferenceEdges r) (x : V) :
    edgeBalance (reservedRawLocalSourceEdges r) x =
      edgeBalance (reservedRawActiveReferenceEdges r) x +
        propInt (x = (reservedStrongSelectedStartingRecord r).record.initial) -
          propInt (x = requestVertex r) := by
  have hbase := reservedRawActiveReference_biUnique r
  have hswitch := reservedRawLocalSwitch_biUnique r
  have hwhole := reservedRawLocalSource_biUnique r
  have hdisj : Disjoint
      (reservedRawActiveReferenceEdges r \ reservedRawRequestBackwardEdges r)
      (reservedRawOwnerAttachment r).forwardEdges := by
    apply Set.disjoint_left.2
    intro e he hf
    exact Set.disjoint_left.1
      ((reservedRawOwnerAttachment r).forwardEdges_disjoint_reference
        (popularAuxiliary_hasBoundaryIncidence L hL.legal)
        (reservedStrongSelectedStartingRecord r).record_mem_ladder) hf
      (reservedRawActiveReference_subset_reference r he.1)
  have hcalc := edgeBalance_sdiff_union_eq_add_sub hB hbase.2 hbase.1
    hswitch.2 hswitch.1 hdisj x
  have hdelta := reservedRawRequest_direction_balance r x
  have hadd := edgeBalance_sdiff_union_eq_add_sub
    (E := reservedRawLocalSwitchEdges r) (B := ∅)
    (F := (reservedRawOwnerAttachment r).sourcePrefix.edgeSet)
    (Set.empty_subset _) hswitch.2 hswitch.1
    (by simpa only [Set.sdiff_empty, reservedRawLocalSourceEdges] using hwhole.2)
    (by simpa only [Set.sdiff_empty, reservedRawLocalSourceEdges] using hwhole.1)
    (by simpa only [Set.sdiff_empty] using reservedRawLocalSwitch_disjoint_prefix r) x
  have hempty : edgeBalance (∅ : Set (V × V)) x = 0 := by
    simp [edgeBalance, HasOutgoing, HasIncoming, propInt]
  have hp := (reservedRawOwnerAttachment r).sourcePrefix_balance x
  change edgeBalance (reservedRawLocalSwitchEdges r) x = _ at hcalc
  simp only [Set.sdiff_empty, hempty, sub_zero] at hadd
  change edgeBalance (reservedRawLocalSourceEdges r) x = _ at hadd
  omega

theorem reservedRawLocalSource_positive_source (r : Request J S.cut)
    (hB : reservedRawRequestBackwardEdges r ⊆ reservedRawActiveReferenceEdges r)
    (x : V) (hx : edgeBalance (reservedRawLocalSourceEdges r) x = 1) :
    x ∈ Gamma.source := by
  classical
  by_cases hs : x = (reservedStrongSelectedStartingRecord r).record.initial
  · exact hs ▸ reservedStrongSelectedStartingRecord_grounded r
  apply reservedRawActiveReference_positive_source r x
  have hbalance := reservedRawLocalSource_balance r hB x
  have hupper : edgeBalance (reservedRawActiveReferenceEdges r) x ≤ 1 := by
    unfold edgeBalance propInt
    split_ifs <;> omega
  have hnonneg : 0 ≤ propInt (x = requestVertex r) := by
    unfold propInt
    split_ifs <;> omega
  simp only [propInt, if_neg hs] at hbalance
  change 0 ≤ if x = requestVertex r then (1 : ℤ) else 0 at hnonneg
  omega

theorem reservedRawLocalSource_request_balance (r : Request J S.cut)
    (hB : reservedRawRequestBackwardEdges r ⊆ reservedRawActiveReferenceEdges r) :
    edgeBalance (reservedRawLocalSourceEdges r) (requestVertex r) = -1 := by
  have hne : requestVertex r ≠ (reservedStrongSelectedStartingRecord r).record.initial :=
    fun h ↦ reservedRawRequestVertex_not_mem_startingRecord r
      (h ▸ (reservedStrongSelectedStartingRecord r).record.initial_mem_support)
  rw [reservedRawLocalSource_balance r hB, reservedRawActiveReference_balance_request]
  simp only [propInt, if_neg hne]
  norm_num

theorem reservedRawLocalSource_no_reverseRay (r : Request J S.cut) :
    ¬ ContainsReverseDirectedRay (reservedRawLocalSourceEdges r) := by
  have hsub : reservedRawLocalSourceEdges r ⊆ (reservedRawOwnerAttachment r).sourceEdges := by
    intro e he
    rcases he with (he | he) | he
    · have hr := reservedRawActiveReference_retained r he
      exact Or.inl (Or.inl ⟨reservedRawRetained_subset_ownerDeleted r hr,
        reservedRawRetained_not_backward r hr⟩)
    · exact Or.inl (Or.inr he)
    · exact Or.inr he
  rintro ⟨p, hp⟩
  exact (reservedRawOwnerAttachment r).sourceEdges_not_containsReverseDirectedRay
    (reservedStrongSelectedStartingRecord r).record_mem_ladder ⟨p, fun n ↦ hsub (hp n)⟩

/-- Once backward coverage is proved, the local sink is genuinely source-rooted. -/
theorem reservedRawLocalSource_request_rooted (r : Request J S.cut)
    (hB : reservedRawRequestBackwardEdges r ⊆ reservedRawActiveReferenceEdges r) :
    ∃ a ∈ Gamma.source, Relation.ReflTransGen
      (fun x y ↦ (x, y) ∈ reservedRawLocalSourceEdges r) a (requestVertex r) := by
  have hsink := edgeBalance_eq_neg_one_iff.mp (reservedRawLocalSource_request_balance r hB)
  exact GroundingFinitePerturbationRooting.sink_rooted_of_noReverseRay
    (reservedRawLocalSourceEdges r) Gamma.source
    ((reservedRawLocalSource_subset_simultaneous r).trans reservedRawSimultaneousEdges_subset_adj)
    (reservedRawLocalSource_biUnique r) (reservedRawLocalSource_no_reverseRay r)
    (reservedRawLocalSource_positive_source r hB) (Or.inr hsink.1) hsink.2

/-- All actual requests are source-rooted in the unstopped raw relation.
Stopping at the final separating boundary is deliberately not claimed. -/
theorem canonicalDeferredLadder_rawRequest_rooted_unstopped
    (preferred : Stage kappa → Option V)
    (hkappa : kappa.IsRegular) (huncountable : aleph0 < kappa)
    (hNoEnter : Gamma.NoEdgeEnters Gamma.source)
    (hL : IsKappaHindrance (canonicalDeferredLadder Gamma kappa preferred))
    (S : Popular.PopularSeparator
      (popularAuxiliaryIndexed (canonicalDeferredLadder Gamma kappa preferred) hL))
    (r : Request
      (popularAuxiliaryInput (canonicalDeferredLadder Gamma kappa preferred) hL.legal) S.cut) :
    ∃ a ∈ Gamma.source, Relation.ReflTransGen
      (fun x y ↦ (x, y) ∈ reservedRawSimultaneousEdges
        (L := canonicalDeferredLadder Gamma kappa preferred) (hL := hL) (S := S))
      a (requestVertex r) := by
  obtain ⟨a, ha, hreach⟩ := reservedRawLocalSource_request_rooted r
    (canonicalDeferredLadder_rawBackward_subset_activeReference
      preferred hkappa huncountable hNoEnter hL S r)
  exact ⟨a, ha, Relation.ReflTransGen.mono
    (fun _ _ he ↦ reservedRawLocalSource_subset_simultaneous r he) _ _ hreach⟩

/-- The actual request sink has an incoming ambient edge, so normalization
also excludes it from the original source. -/
theorem canonicalDeferredLadder_rawRequest_not_source
    (preferred : Stage kappa → Option V)
    (hkappa : kappa.IsRegular) (huncountable : aleph0 < kappa)
    (hNoEnter : Gamma.NoEdgeEnters Gamma.source)
    (hL : IsKappaHindrance (canonicalDeferredLadder Gamma kappa preferred))
    (S : Popular.PopularSeparator
      (popularAuxiliaryIndexed (canonicalDeferredLadder Gamma kappa preferred) hL))
    (r : Request
      (popularAuxiliaryInput (canonicalDeferredLadder Gamma kappa preferred) hL.legal) S.cut) :
    requestVertex r ∉ Gamma.source := by
  have hB := canonicalDeferredLadder_rawBackward_subset_activeReference
    preferred hkappa huncountable hNoEnter hL S r
  obtain ⟨x, hx⟩ := (edgeBalance_eq_neg_one_iff.mp
    (reservedRawLocalSource_request_balance r hB)).1
  exact hNoEnter (reservedRawSimultaneousEdges_subset_adj
    (reservedRawLocalSource_subset_simultaneous r hx))

#print axioms reservedRawLocalSource_balance
#print axioms reservedRawLocalSource_request_rooted
#print axioms canonicalDeferredLadder_rawRequest_rooted_unstopped
#print axioms canonicalDeferredLadder_rawRequest_not_source

end Erdos599.DWeb.KappaLadder.Deferred
