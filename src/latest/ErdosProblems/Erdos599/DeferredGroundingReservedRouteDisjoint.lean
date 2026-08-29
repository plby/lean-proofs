/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.DeferredGroundingReservedRelevantPruning
import ErdosProblems.Erdos599.DeferredGroundingSelectedAssembly
import ErdosProblems.Erdos599.DeferredGroundingSeparatorGeometry
import ErdosProblems.Erdos599.GroundingErasedCarrierRank

/-!
# The reserved deferred record is disjoint from the simultaneous routes

The final deferred controls exclude every selected auxiliary path which
meets the reserved carrier away from its request apex.  The carrier avoids
the popular cut, so the apex is excluded as well.  This file transports that
auxiliary statement to the literal original-vertex footprints used by the
deferred simultaneous switch.

Consequently no selected decoded edge is incident with the reserved record.
Every edge of that record therefore survives the symmetric difference, and
the record support is closed in both directions in the switched relation.
These are the concrete preservation facts needed by the final simultaneous
component exchange; no realization or compiler premise is introduced.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace DWeb
namespace KappaLadder
namespace Deferred

open _root_.Erdos599.DirectedPath
open _root_.Erdos599.Alternating
open PopularGroundingBridge GroundingErasedCarrierRank
open GroundingSimultaneousDecode

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}
variable {L : Gamma.KappaLadder kappa} {hL : IsKappaHindrance L}
variable {S : Popular.PopularSeparator (popularAuxiliaryIndexed L hL)}

local notation "J" => popularAuxiliaryInput L hL.legal
local notation "U" => popularAuxiliaryIndexed L hL
local notation "K" => reservedGroundedCarrierControls L hL S
local notation "R" => canonicalReservedRecord L hL S

private theorem gadgetFootprint_eq_gadgetCarrier (a : J.LV) :
    J.gadgetFootprint a = J.gadgetCarrier a := by
  cases a <;> rfl

/-- The original-vertex footprint of every actually selected deferred route
is disjoint from the actual reserved record. -/
theorem reservedSelectedPath_pathFootprint_disjoint_record
    (r : Request J S.cut) :
    Disjoint
      (J.pathFootprint
        (GroundingAssembly.selectedPath U S K r))
      R.record.support := by
  let p := GroundingAssembly.selectedPath U S K r
  have hpStart : p.start ∈ J.lambda.source :=
    (GroundingAssembly.selectedWarp U S K).starts_in_source ⟨r, rfl⟩
  apply Set.disjoint_left.mpr
  intro z hzFootprint hzRecord
  simp only [PopularAuxiliary.Input.pathFootprint, Set.mem_iUnion] at hzFootprint
  obtain ⟨a, haPath, hza⟩ := hzFootprint
  have hzaCarrier : z ∈ J.gadgetCarrier a := by
    rw [← gadgetFootprint_eq_gadgetCarrier a]
    exact hza
  rcases J.gadget_mem_ladderTrace_or_proxy_eq_of_mem_carrier_of_mem_support
      (popularAuxiliary_proxyPathsFaithful L hL)
      p hpStart haPath R.record_mem_ladder hzaCarrier hzRecord with
    haTrace | ⟨i, haProxy, hproxyRecord⟩
  · have haNotApex : a ≠ requestAuxVertex r := by
      intro haApex
      exact Set.disjoint_left.mp R.trace_disjoint haTrace
        (haApex ▸ requestAuxVertex_mem_cut r)
    exact (reservedSelectedPath_no_offApex_reserved_contact r
      (Or.inl haTrace) haNotApex) haPath
  · have hpStartProxy : p.start = PopularAuxiliary.Input.LambdaVertex.proxy i :=
      J.proxy_mem_support_eq_start p hpStart (haProxy ▸ haPath)
    rcases R.source_represents with
      ⟨q, hrecordFinite, _hsourceFinite⟩ |
      ⟨j, hrecordInfinite, hsourceProxy⟩
    · obtain ⟨ray, hproxyRay⟩ := J.proxy_isRay i
      have hfalse : (Sum.inr ray : Gamma.DPath) = Sum.inl q :=
        hproxyRay.symm.trans (hproxyRecord.trans hrecordFinite)
      cases hfalse
    · have hij : i = j := by
        apply Subtype.ext
        simpa only [popularAuxiliaryInput, infinitePath] using
          hproxyRecord.trans hrecordInfinite
      apply reservedSelectedPath_start_ne_reservedSource r
      rw [hpStartProxy, hij, hsourceProxy]

/-- No selected decoded edge is incident with the reserved record. -/
theorem reservedSelectedPath_decodedIncident_disjoint_record
    (r : Request J S.cut) :
    Disjoint
      (RelationDecomposition.IncidentVertices
        (J.decodedRouteEdges
          (GroundingAssembly.selectedPath U S K r)))
      R.record.support :=
  (reservedSelectedPath_pathFootprint_disjoint_record r).mono
    (J.decodedRouteEdges_incidentVertices_subset_pathFootprint
      (GroundingAssembly.selectedPath U S K r))
    Set.Subset.rfl

/-- The union of all selected decoded route edges is still completely
nonincident with the reserved record. -/
theorem reservedSelectedDecodedRouteEdges_incident_disjoint_record :
    Disjoint
      (RelationDecomposition.IncidentVertices
        (selectedDecodedRouteEdges L hL S K))
      R.record.support := by
  apply Set.disjoint_left.mpr
  intro x hxIncident hxRecord
  rcases hxIncident with ⟨y, hxy | hyx⟩
  · simp only [selectedDecodedRouteEdges, Set.mem_iUnion] at hxy
    obtain ⟨r, hxy⟩ := hxy
    exact Set.disjoint_left.mp
      (reservedSelectedPath_decodedIncident_disjoint_record r)
      ⟨y, Or.inl hxy⟩ hxRecord
  · simp only [selectedDecodedRouteEdges, Set.mem_iUnion] at hyx
    obtain ⟨r, hyx⟩ := hyx
    exact Set.disjoint_left.mp
      (reservedSelectedPath_decodedIncident_disjoint_record r)
      ⟨y, Or.inr hyx⟩ hxRecord

private theorem reservedRecord_familyEdge_endpoints
    {x y : V} (hxy : (x, y) ∈ J.familyEdges)
    (hx : x ∈ R.record.support) : y ∈ R.record.support := by
  obtain ⟨Y, hYL, hxyY⟩ := hxy
  have hxY : x ∈ Y.support := (Y.edgeSet_subset_support_prod hxyY).1
  have hrecordY : R.record = Y :=
    DWeb.IsWarp.eq_of_mem_support J.ladder.disjoint
      R.record_mem_ladder hYL hx hxY
  rw [hrecordY]
  exact (Y.edgeSet_subset_support_prod hxyY).2

private theorem reservedRecord_familyEdge_endpoints_rev
    {x y : V} (hxy : (x, y) ∈ J.familyEdges)
    (hy : y ∈ R.record.support) : x ∈ R.record.support := by
  obtain ⟨Y, hYL, hxyY⟩ := hxy
  have hyY : y ∈ Y.support := (Y.edgeSet_subset_support_prod hxyY).2
  have hrecordY : R.record = Y :=
    DWeb.IsWarp.eq_of_mem_support J.ladder.disjoint
      R.record_mem_ladder hYL hy hyY
  rw [hrecordY]
  exact (Y.edgeSet_subset_support_prod hxyY).1

/-- Every original edge of the reserved record survives the literal
simultaneous symmetric difference. -/
theorem canonicalReservedRecord_edgeSet_subset_simultaneousSelectedSwitchData :
    R.record.edgeSet ⊆
      (simultaneousSelectedSwitchData L hL S K).edges := by
  intro e heRecord
  rw [simultaneousSelectedSwitchData_edges, mem_edgeSymmDiff]
  left
  constructor
  · exact ⟨R.record, R.record_mem_ladder, heRecord⟩
  · intro heSelected
    have htailIncident : e.1 ∈
        RelationDecomposition.IncidentVertices
          (selectedDecodedRouteEdges L hL S K) :=
      ⟨e.2, Or.inl heSelected⟩
    exact Set.disjoint_left.mp
      reservedSelectedDecodedRouteEdges_incident_disjoint_record
      htailIncident (R.record.edgeSet_subset_support_prod heRecord).1

/-- A switched edge whose tail is on the reserved record stays on it. -/
theorem simultaneousSelectedSwitchData_edge_head_mem_reservedRecord
    {x y : V} (hx : x ∈ R.record.support)
    (hxy : (x, y) ∈ (simultaneousSelectedSwitchData L hL S K).edges) :
    y ∈ R.record.support := by
  rw [simultaneousSelectedSwitchData_edges, mem_edgeSymmDiff] at hxy
  rcases hxy with hbase | hselected
  · exact reservedRecord_familyEdge_endpoints hbase.1 hx
  · exact False.elim <| Set.disjoint_left.mp
      reservedSelectedDecodedRouteEdges_incident_disjoint_record
      ⟨y, Or.inl hselected.1⟩ hx

/-- The reverse closure needed to identify the reserved record as a whole
component of any realization of the simultaneous relation. -/
theorem simultaneousSelectedSwitchData_edge_tail_mem_reservedRecord
    {x y : V} (hy : y ∈ R.record.support)
    (hxy : (x, y) ∈ (simultaneousSelectedSwitchData L hL S K).edges) :
    x ∈ R.record.support := by
  rw [simultaneousSelectedSwitchData_edges, mem_edgeSymmDiff] at hxy
  rcases hxy with hbase | hselected
  · exact reservedRecord_familyEdge_endpoints_rev hbase.1 hy
  · exact False.elim <| Set.disjoint_left.mp
      reservedSelectedDecodedRouteEdges_incident_disjoint_record
      ⟨x, Or.inr hselected.1⟩ hy

end Deferred
end KappaLadder
end DWeb
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.Deferred.reservedSelectedPath_pathFootprint_disjoint_record
#print axioms
  Erdos599.DWeb.KappaLadder.Deferred.reservedSelectedDecodedRouteEdges_incident_disjoint_record
#print axioms
  Erdos599.DWeb.KappaLadder.Deferred.canonicalReservedRecord_edgeSet_subset_simultaneousSelectedSwitchData
#print axioms
  Erdos599.DWeb.KappaLadder.Deferred.simultaneousSelectedSwitchData_edge_head_mem_reservedRecord

