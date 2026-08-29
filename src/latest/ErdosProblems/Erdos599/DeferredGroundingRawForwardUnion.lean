/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.DeferredGroundingRawOwnerSeparation

/-!
# Degree bounds for the actual simultaneous raw forward insertion

Auxiliary head ports identify the request owning an incoming forward edge.
At a departure, either a unique non-proxy port identifies the request, or
the actual attachment lies on its private starting record. Thus the entire
forward union is biunique, without deleting any repeated physical vertex.
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

theorem reservedRaw_selectedPaths_disjoint (r s : Request J S.cut) (hrs : r ≠ s) :
    Disjoint (strongSelectedPath U S K r).support (strongSelectedPath U S K s).support := by
  apply (strongSelectedWarp U S K).disjoint ⟨r, rfl⟩ ⟨s, rfl⟩
  intro hpq
  have hfinish := congrArg FinitePath.finish hpq
  rw [strongSelectedPath_finish, strongSelectedPath_finish] at hfinish
  exact hrs (GroundingSelection.requestAuxVertex_injective hfinish)

/-- Shared forward heads identify the actual owning request. -/
theorem reservedRawForward_common_head_request_eq (r s : Request J S.cut) {x y z : V}
    (hxy : (x, y) ∈ (reservedRawOwnerAttachment r).forwardEdges)
    (hzy : (z, y) ∈ (reservedRawOwnerAttachment s).forwardEdges) : r = s := by
  by_contra hrs
  obtain ⟨⟨a, b, hab, hchoice⟩, hne⟩ :=
    (reservedRawOwnerAttachment r).forwardEdges_subset_original_properConnectors hxy
  obtain ⟨⟨c, d, hcd, hchoice'⟩, hne'⟩ :=
    (reservedRawOwnerAttachment s).forwardEdges_subset_original_properConnectors hzy
  have hboundary := popularAuxiliary_hasBoundaryIncidence L hL.legal
  have hbd : b = d :=
    (hboundary.forward_head_port (x := x)
      ((strongSelectedPath U S K r).edgeSet_subset_adj hab)
      ((J).chosenConnector?_eq_some hchoice) hne).unique
        (hboundary.forward_head_port (x := z)
          ((strongSelectedPath U S K s).edgeSet_subset_adj hcd)
          ((J).chosenConnector?_eq_some hchoice') hne')
  exact Set.disjoint_left.1 (reservedRaw_selectedPaths_disjoint r s hrs)
    ((strongSelectedPath U S K r).edgeSet_subset_support_prod hab).2
    (hbd.symm ▸ ((strongSelectedPath U S K s).edgeSet_subset_support_prod hcd).2)

/-- Shared forward tails also identify the request, including its possible
proxy attachment at an interior point of a recorded ray. -/
theorem reservedRawForward_common_tail_request_eq (r s : Request J S.cut) {x y z : V}
    (hxy : (x, y) ∈ (reservedRawOwnerAttachment r).forwardEdges)
    (hxz : (x, z) ∈ (reservedRawOwnerAttachment s).forwardEdges) : r = s := by
  by_contra hrs
  have hxyFull := hxy
  rcases hxy with hxy | hxy
  · have hx : x = (reservedRawOwnerAttachment r).anchor :=
      congrArg Prod.fst (Set.mem_singleton_iff.1 hxy)
    exact (reservedRawOwner_forward_other_avoids_record r s hrs hxz).1
      (hx.symm ▸ (reservedRawOwnerAttachment r).anchor_mem_owner)
  rcases hxz with hxz | hxz
  · have hx : x = (reservedRawOwnerAttachment s).anchor :=
      congrArg Prod.fst (Set.mem_singleton_iff.1 hxz)
    exact (reservedRawOwner_forward_other_avoids_record s r
      (fun h ↦ hrs h.symm) hxyFull).1
      (hx.symm ▸ (reservedRawOwnerAttachment s).anchor_mem_owner)
  obtain ⟨⟨a, b, hab, hchoice⟩, hne⟩ := hxy
  obtain ⟨⟨c, d, hcd, hchoice'⟩, hne'⟩ := hxz
  have hboundary := popularAuxiliary_hasBoundaryIncidence L hL.legal
  have hport : (J).RawTailPort a x := by
    rcases hboundary.forward_tail_port_or_proxy
        ((reservedRawOwnerAttachment r).tail.edgeSet_subset_adj hab)
        ((J).chosenConnector?_eq_some hchoice) hne with h | ⟨i, rfl, _hi⟩
    · exact h
    · exact False.elim ((reservedRawOwnerAttachment r).tail_no_proxy i
        ((reservedRawOwnerAttachment r).tail.edgeSet_subset_support_prod hab).1)
  have hport' : (J).RawTailPort c x := by
    rcases hboundary.forward_tail_port_or_proxy
        ((reservedRawOwnerAttachment s).tail.edgeSet_subset_adj hcd)
        ((J).chosenConnector?_eq_some hchoice') hne' with h | ⟨i, rfl, _hi⟩
    · exact h
    · exact False.elim ((reservedRawOwnerAttachment s).tail_no_proxy i
        ((reservedRawOwnerAttachment s).tail.edgeSet_subset_support_prod hcd).1)
  have hac : a = c := hport.unique hport'
  exact Set.disjoint_left.1 (reservedRaw_selectedPaths_disjoint r s hrs)
    ((reservedRawOwnerAttachment r).tail_support_subset
      ((reservedRawOwnerAttachment r).tail.edgeSet_subset_support_prod hab).1)
    (hac.symm ▸ (reservedRawOwnerAttachment s).tail_support_subset
      ((reservedRawOwnerAttachment s).tail.edgeSet_subset_support_prod hcd).1)

def reservedRawForwardEdges : Set (V × V) :=
  ⋃ r : Request J S.cut, (reservedRawOwnerAttachment r).forwardEdges

/-- The literal union of every selected raw forward insertion is biunique. -/
theorem reservedRawForwardEdges_biUnique :
    Relator.BiUnique (fun x y ↦ (x, y) ∈
      reservedRawForwardEdges (L := L) (hL := hL) (S := S)) := by
  have hboundary := popularAuxiliary_hasBoundaryIncidence L hL.legal
  constructor
  · intro x z y hxy hzy
    obtain ⟨r, hr⟩ := Set.mem_iUnion.1 hxy
    obtain ⟨s, hs⟩ := Set.mem_iUnion.1 hzy
    have hrs := reservedRawForward_common_head_request_eq r s hr hs
    subst s
    exact ((reservedRawOwnerAttachment r).forwardEdges_biUnique hboundary
      (reservedStrongSelectedStartingRecord r).record_mem_ladder).1 hr hs
  · intro x y z hxy hxz
    obtain ⟨r, hr⟩ := Set.mem_iUnion.1 hxy
    obtain ⟨s, hs⟩ := Set.mem_iUnion.1 hxz
    have hrs := reservedRawForward_common_tail_request_eq r s hr hs
    subst s
    exact ((reservedRawOwnerAttachment r).forwardEdges_biUnique hboundary
      (reservedStrongSelectedStartingRecord r).record_mem_ladder).2 hr hs

theorem reservedRawForwardEdges_disjoint_reference :
    Disjoint (reservedRawForwardEdges (L := L) (hL := hL) (S := S)) (J).familyEdges := by
  apply Set.disjoint_left.2
  intro e he href
  obtain ⟨r, hr⟩ := Set.mem_iUnion.1 he
  exact Set.disjoint_left.1 ((reservedRawOwnerAttachment r).forwardEdges_disjoint_reference
    (popularAuxiliary_hasBoundaryIncidence L hL.legal)
    (reservedStrongSelectedStartingRecord r).record_mem_ladder) hr href

#print axioms reservedRawForward_common_tail_request_eq
#print axioms reservedRawForwardEdges_biUnique

end Erdos599.DWeb.KappaLadder.Deferred
