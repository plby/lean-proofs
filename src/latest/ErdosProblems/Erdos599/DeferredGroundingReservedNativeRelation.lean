/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.DeferredGroundingReservedRelevantPruning
import ErdosProblems.Erdos599.GroundingErasedCarrierRank
import ErdosProblems.Erdos599.GroundingErasedForwardConflict

/-!
# Exact preservation of the reserved record in the native deferred switch

The final selector uses `strongSelectedPath`, not the older ordinary
selected family. Its literal decoded carrier misses the reserved record.
Thus none of the erased backward edges or forward-conflict cuts can affect
that record. Stopping at a frontier disjoint from it preserves every record
edge and permits no new incident edge.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599.DWeb.KappaLadder.Deferred

open _root_.Erdos599.DirectedPath Alternating PopularGroundingBridge
open GroundingSimultaneousDecode GroundingErasedDecode
open GroundingErasedCarrierRank GroundingErasedSwitchRelation

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}
variable {L : Gamma.KappaLadder kappa} {hL : IsKappaHindrance L}
variable {S : Popular.PopularSeparator (popularAuxiliaryIndexed L hL)}

local notation "J" => popularAuxiliaryInput L hL.legal
local notation "U" => popularAuxiliaryIndexed L hL
local notation "K" => reservedGroundedCarrierControls L hL S
local notation "R" => canonicalReservedRecord L hL S

/-- The final strong-selected route, including any proxy gadget, misses
the actual reserved record in original-vertex carrier. -/
theorem reservedStrongSelectedPath_decodedCarrier_disjoint_record
    (r : Request J S.cut) :
    Disjoint ((J).decodedVertexCarrier (strongSelectedPath U S K r))
      (R).record.support := by
  let p := strongSelectedPath U S K r
  have hpStart : p.start ∈ (J).lambda.source :=
    (strongSelectedWarp U S K).starts_in_source ⟨r, rfl⟩
  apply Set.disjoint_left.mpr
  intro z hzCarrier hzRecord
  simp only [PopularAuxiliary.Input.decodedVertexCarrier, Set.mem_iUnion] at hzCarrier
  obtain ⟨a, haPath, hza⟩ := hzCarrier
  rcases (J).gadget_mem_ladderTrace_or_proxy_eq_of_mem_carrier_of_mem_support
      (popularAuxiliary_proxyPathsFaithful L hL)
      p hpStart haPath (R).toAuxiliarySourceRecord.record_mem_ladder hza hzRecord with
    haTrace | ⟨i, haProxy, hproxyRecord⟩
  · have haNotApex : a ≠ requestAuxVertex r := by
      intro haApex
      exact Set.disjoint_left.mp (R).trace_disjoint haTrace
        (haApex ▸ requestAuxVertex_mem_cut r)
    exact (reservedStrongSelectedPath_no_offApex_reserved_contact r
      (Or.inl haTrace) haNotApex) haPath
  · have hpStartProxy : p.start = PopularAuxiliary.Input.LambdaVertex.proxy i :=
      (J).proxy_mem_support_eq_start p hpStart (haProxy ▸ haPath)
    rcases (R).source_represents with
      ⟨q, hrecordFinite, _hsourceFinite⟩ | ⟨j, hrecordInfinite, hsourceProxy⟩
    · obtain ⟨ray, hproxyRay⟩ := (J).proxy_isRay i
      have hfalse : (Sum.inr ray : Gamma.DPath) = Sum.inl q :=
        hproxyRay.symm.trans (hproxyRecord.trans hrecordFinite)
      cases hfalse
    · have hij : i = j := by
        apply Subtype.ext
        simpa only [popularAuxiliaryInput, infinitePath] using
          hproxyRecord.trans hrecordInfinite
      apply reservedStrongSelectedPath_start_ne_reservedSource r
      rw [hpStartProxy, hij, hsourceProxy]

/-- No selected coloured edge of the native erased relation is incident
with the reserved record, for any stopping frontier. -/
theorem erasedSelectedDirectionEdgesAt_not_incident_reservedRecord
    (T : Set V) (d : Direction) {e : V × V}
    (he : e ∈ erasedSelectedDirectionEdgesAt U S K T d) :
    e.1 ∉ (R).record.support ∧ e.2 ∉ (R).record.support := by
  obtain ⟨c, he⟩ := Set.mem_iUnion.mp he
  let r := chosenRequest c.1
  have hePath : e ∈ (selectedErasedCompression U S K r).path.edgeSet := by
    rw [(selectedErasedCompression U S K r).path.edgeSet_eq_directionEdges_union]
    cases d with
    | forward => exact Or.inl he
    | backward => exact Or.inr he
  have hends := selectedErasedRouteEdge_endpoints_mem U S K r hePath
  have hdisj := reservedStrongSelectedPath_decodedCarrier_disjoint_record r
  exact ⟨fun h ↦ Set.disjoint_left.mp hdisj hends.1 h,
    fun h ↦ Set.disjoint_left.mp hdisj hends.2 h⟩

/-- Every record edge survives all native deletions. -/
theorem canonicalReservedRecord_edgeSet_subset_nativeSwitch
    (T : Set V) (hT : Disjoint T (R).record.support) :
    (R).record.edgeSet ⊆ erasedSelectedSwitchedEdgesAt U S K T := by
  intro e he
  have hends := (R).record.edgeSet_subset_support_prod he
  have heBase : e ∈ residualLadderEdges U S := by
    refine ⟨⟨(R).record, (R).toAuxiliarySourceRecord.record_mem_ladder, he⟩, ?_⟩
    intro heCE
    have htrace := (PopularSwitching.edge_mem_ladderTrace_iff
      J (R).record e.1 e.2).mpr he
    exact Set.disjoint_left.mp (R).trace_disjoint htrace heCE.1
  left
  refine ⟨heBase, ?_⟩
  rintro (heBackward | heConflict | heBoundary)
  · exact (erasedSelectedDirectionEdgesAt_not_incident_reservedRecord
      T .backward heBackward).1 hends.1
  · obtain ⟨_heBase, f, hf, htail | hhead⟩ := heConflict
    · have hn := erasedSelectedDirectionEdgesAt_not_incident_reservedRecord
        T .forward (erasedSelectedRetainedForwardEdgesAt_subset_forward U S K T hf)
      exact hn.1 (htail ▸ hends.1)
    · have hn := erasedSelectedDirectionEdgesAt_not_incident_reservedRecord
        T .forward (erasedSelectedRetainedForwardEdgesAt_subset_forward U S K T hf)
      exact hn.2 (hhead ▸ hends.2)
  · exact Set.disjoint_left.mp hT heBoundary.2 hends.1

/-- A native edge incident at either end with the reserved record is
exactly one of that record's old edges. -/
theorem nativeSwitch_edge_mem_reservedRecord_of_incident
    (T : Set V) {e : V × V}
    (he : e ∈ erasedSelectedSwitchedEdgesAt U S K T)
    (hinc : e.1 ∈ (R).record.support ∨ e.2 ∈ (R).record.support) :
    e ∈ (R).record.edgeSet := by
  rcases he with he | he
  · obtain ⟨p, hp, hep⟩ := he.1.1
    have hpends := p.edgeSet_subset_support_prod hep
    have hpEq : p = (R).record := by
      rcases hinc with htail | hhead
      · exact DWeb.IsWarp.eq_of_mem_support (J).ladder.disjoint hp
          (R).toAuxiliarySourceRecord.record_mem_ladder
          hpends.1 htail
      · exact DWeb.IsWarp.eq_of_mem_support (J).ladder.disjoint hp
          (R).toAuxiliarySourceRecord.record_mem_ladder
          hpends.2 hhead
    simpa only [hpEq] using hep
  · have hn := erasedSelectedDirectionEdgesAt_not_incident_reservedRecord T .forward he.1
    exact (hinc.elim hn.1 hn.2).elim

/-- Exact local edge identity, not only closure of the reserved carrier. -/
theorem nativeSwitch_edge_iff_of_incident_reservedRecord
    (T : Set V) (hT : Disjoint T (R).record.support) {e : V × V}
    (hinc : e.1 ∈ (R).record.support ∨ e.2 ∈ (R).record.support) :
    e ∈ erasedSelectedSwitchedEdgesAt U S K T ↔ e ∈ (R).record.edgeSet :=
  ⟨fun he ↦ nativeSwitch_edge_mem_reservedRecord_of_incident T he hinc,
    fun he ↦ canonicalReservedRecord_edgeSet_subset_nativeSwitch T hT he⟩

/-- The concrete deferred frontier satisfies the disjointness required by
the exact native preservation theorem. -/
theorem canonicalReservedRecord_edgeSet_subset_reservedNativeSwitch :
    (R).record.edgeSet ⊆ erasedSelectedSwitchedEdgesAt U S K
      (reservedStrongSelectedRelevantBB (L := L) (hL := hL) (S := S)) :=
  canonicalReservedRecord_edgeSet_subset_nativeSwitch _
    canonicalReservedRecord_disjoint_reservedStrongSelectedRelevantBB

#print axioms reservedStrongSelectedPath_decodedCarrier_disjoint_record
#print axioms nativeSwitch_edge_iff_of_incident_reservedRecord
#print axioms canonicalReservedRecord_edgeSet_subset_reservedNativeSwitch

end Erdos599.DWeb.KappaLadder.Deferred
