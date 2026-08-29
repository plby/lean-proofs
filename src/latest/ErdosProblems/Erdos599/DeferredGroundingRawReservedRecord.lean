/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.DeferredGroundingRawSimultaneousRelation
import ErdosProblems.Erdos599.DeferredGroundingReservedNativeRelation

/-!
# Exact preservation of the unused reserved record by the raw switch

Only the saved raw carrier-avoidance theorem is reused from the native
relation development. No erased edge relation is identified with the raw
one. All cuts, whole-owner deletions, backward deletions and insertions are
checked separately against the actual reserved record.
-/

noncomputable section

namespace Erdos599.DWeb.KappaLadder.Deferred

open Set _root_.Erdos599.DirectedPath Alternating
open PopularAuxiliary.Input PopularGroundingBridge GroundingSimultaneousDecode

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}
variable {L : Gamma.KappaLadder kappa} {hL : IsKappaHindrance L}
variable {S : Popular.PopularSeparator (popularAuxiliaryIndexed L hL)}

local notation "J" => popularAuxiliaryInput L hL.legal
local notation "U" => popularAuxiliaryIndexed L hL
local notation "K" => reservedGroundedCarrierControls L hL S
local notation "R" => canonicalReservedRecord L hL S
local notation "E" => reservedRawSimultaneousEdges (L := L) (hL := hL) (S := S)

theorem reservedRawOwner_record_ne_reserved (r : Request J S.cut) :
    (reservedStrongSelectedStartingRecord r).record ≠ (R).record := by
  intro hrecords
  have hanchor := (reservedRawOwnerAttachment r).forwardEdges_endpoints_mem_originalCarrier
    (e := ((reservedRawOwnerAttachment r).anchor, (reservedRawOwnerAttachment r).nextVertex))
    (Or.inl rfl)
  exact Set.disjoint_left.1 (reservedStrongSelectedPath_decodedCarrier_disjoint_record r)
    hanchor.1 (hrecords ▸ (reservedRawOwnerAttachment r).anchor_mem_owner)

theorem reservedRawOwner_record_disjoint_reserved (r : Request J S.cut) :
    Disjoint (reservedStrongSelectedStartingRecord r).record.support (R).record.support :=
  (J).ladder.disjoint (reservedStrongSelectedStartingRecord r).record_mem_ladder
    (R).toAuxiliarySourceRecord.record_mem_ladder (reservedRawOwner_record_ne_reserved r)

theorem reservedRawForward_not_incident_reserved {e : V × V}
    (he : e ∈ reservedRawForwardEdges (L := L) (hL := hL) (S := S)) :
    e.1 ∉ (R).record.support ∧ e.2 ∉ (R).record.support := by
  obtain ⟨r, hr⟩ := Set.mem_iUnion.1 he
  have hends := (reservedRawOwnerAttachment r).forwardEdges_endpoints_mem_originalCarrier hr
  have hdisj := reservedStrongSelectedPath_decodedCarrier_disjoint_record r
  exact ⟨fun hx ↦ Set.disjoint_left.1 hdisj hends.1 hx,
    fun hy ↦ Set.disjoint_left.1 hdisj hends.2 hy⟩

theorem reservedRawBackward_not_incident_reserved {e : V × V}
    (he : e ∈ reservedRawBackwardEdges (L := L) (hL := hL) (S := S)) :
    e.1 ∉ (R).record.support ∧ e.2 ∉ (R).record.support := by
  obtain ⟨r, hr⟩ := Set.mem_iUnion.1 he
  have hrepresented : e ∈ (J).representedEdges (strongSelectedPath U S K r) :=
    ⟨(reservedRawOwnerAttachment r).tail_support_subset hr.1, hr.2⟩
  have hends := (J).decodedRouteEdge_endpoints_mem_decodedVertexCarrier
    (strongSelectedPath U S K r) (Or.inl hrepresented)
  have hdisj := reservedStrongSelectedPath_decodedCarrier_disjoint_record r
  exact ⟨fun hx ↦ Set.disjoint_left.1 hdisj hends.1 hx,
    fun hy ↦ Set.disjoint_left.1 hdisj hends.2 hy⟩

theorem reservedRawPrefix_not_incident_reserved {e : V × V}
    (he : e ∈ reservedRawPrefixEdges (L := L) (hL := hL) (S := S)) :
    e.1 ∉ (R).record.support ∧ e.2 ∉ (R).record.support := by
  obtain ⟨r, hr⟩ := Set.mem_iUnion.1 he
  have hends := (reservedRawOwnerAttachment r).sourcePrefix.edgeSet_subset_support_prod hr
  have hdisj := reservedRawOwner_record_disjoint_reserved r
  exact ⟨fun hx ↦ Set.disjoint_left.1 hdisj
      ((reservedRawOwnerAttachment r).sourcePrefix_support hends.1) hx,
    fun hy ↦ Set.disjoint_left.1 hdisj
      ((reservedRawOwnerAttachment r).sourcePrefix_support hends.2) hy⟩

/-- Every actual reserved-record edge survives all simultaneous raw deletions. -/
theorem reservedRaw_reserved_record_edges_retained :
    (R).record.edgeSet ⊆ reservedRawRetainedEdges (L := L) (hL := hL) (S := S) := by
  intro e he
  refine ⟨⟨⟨⟨(R).record, (R).toAuxiliarySourceRecord.record_mem_ladder, he⟩, ?_⟩, ?_⟩, ?_⟩
  · intro heCut
    exact Set.disjoint_left.1 (R).trace_disjoint
      ((PopularSwitching.edge_mem_ladderTrace_iff J (R).record e.1 e.2).2 he) heCut.1
  · intro heOwner
    obtain ⟨r, hr⟩ := Set.mem_iUnion.1 heOwner
    exact Set.disjoint_left.1 (reservedRawOwner_record_disjoint_reserved r)
      ((reservedStrongSelectedStartingRecord r).record.edgeSet_subset_support_prod hr).1
      ((R).record.edgeSet_subset_support_prod he).1
  · intro heBackward
    exact (reservedRawBackward_not_incident_reserved heBackward).1
      ((R).record.edgeSet_subset_support_prod he).1

/-- The exact global raw relation agrees with the reserved record on every
edge incident with its support. -/
theorem reservedRaw_edge_iff_of_incident_reserved {x y : V}
    (hincident : x ∈ (R).record.support ∨ y ∈ (R).record.support) :
    (x, y) ∈ E ↔ (x, y) ∈ (R).record.edgeSet := by
  constructor
  · intro he
    rcases he with hretained | hforward | hprefix
    · rcases hincident with hx | hy
      · exact (J).referenceEdge_mem_owner_of_tail
          (R).toAuxiliarySourceRecord.record_mem_ladder hretained.1.1.1 hx
      · exact (J).referenceEdge_mem_owner_of_head
          (R).toAuxiliarySourceRecord.record_mem_ladder hretained.1.1.1 hy
    · have hnot := reservedRawForward_not_incident_reserved hforward
      exact False.elim (hincident.elim hnot.1 hnot.2)
    · have hnot := reservedRawPrefix_not_incident_reserved hprefix
      exact False.elim (hincident.elim hnot.1 hnot.2)
  · intro he
    exact Or.inl (reservedRaw_reserved_record_edges_retained he)

theorem reservedRaw_record_forwardClosed {x y : V} (he : (x, y) ∈ E)
    (hx : x ∈ (R).record.support) : y ∈ (R).record.support :=
  ((R).record.edgeSet_subset_support_prod
    ((reservedRaw_edge_iff_of_incident_reserved (Or.inl hx)).1 he)).2

theorem reservedRaw_record_backwardClosed {x y : V} (he : (x, y) ∈ E)
    (hy : y ∈ (R).record.support) : x ∈ (R).record.support :=
  ((R).record.edgeSet_subset_support_prod
    ((reservedRaw_edge_iff_of_incident_reserved (Or.inr hy)).1 he)).1

#print axioms reservedRaw_reserved_record_edges_retained
#print axioms reservedRaw_edge_iff_of_incident_reserved

end Erdos599.DWeb.KappaLadder.Deferred
