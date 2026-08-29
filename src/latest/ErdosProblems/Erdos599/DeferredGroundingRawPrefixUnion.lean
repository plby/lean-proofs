/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.DeferredGroundingRawForwardUnion

/-!
# Simultaneous restoration of all genuine source prefixes

The restored prefixes are pairwise disjoint and lie on their own starting
records. The forward union never enters those records and can leave one
only at its own prefix finish. Hence their union has both degree bounds.
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
local notation "F" => reservedRawForwardEdges (L := L) (hL := hL) (S := S)

def reservedRawPrefixEdges : Set (V × V) :=
  ⋃ r : Request J S.cut, (reservedRawOwnerAttachment r).sourcePrefix.edgeSet

local notation "P" => reservedRawPrefixEdges (L := L) (hL := hL) (S := S)

private theorem prefix_common_vertex_request_eq (r s : Request J S.cut) {x : V}
    (hr : x ∈ (reservedRawOwnerAttachment r).sourcePrefix.support)
    (hs : x ∈ (reservedRawOwnerAttachment s).sourcePrefix.support) : r = s := by
  by_contra hrs
  exact Set.disjoint_left.1
    (reservedRawOwner_prefixes_pairwiseDisjoint (Set.mem_univ r) (Set.mem_univ s) hrs) hr hs

theorem reservedRawPrefixEdges_biUnique : Relator.BiUnique (fun x y ↦ (x, y) ∈ P) := by
  constructor
  · intro x z y hxy hzy
    obtain ⟨r, hr⟩ := Set.mem_iUnion.1 hxy
    obtain ⟨s, hs⟩ := Set.mem_iUnion.1 hzy
    have hrs := prefix_common_vertex_request_eq r s
      ((reservedRawOwnerAttachment r).sourcePrefix.edgeSet_subset_support_prod hr).2
      ((reservedRawOwnerAttachment s).sourcePrefix.edgeSet_subset_support_prod hs).2
    subst s
    exact (Alternating.FinitePath.edgeSet_biUnique
      (reservedRawOwnerAttachment r).sourcePrefix).1 hr hs
  · intro x y z hxy hxz
    obtain ⟨r, hr⟩ := Set.mem_iUnion.1 hxy
    obtain ⟨s, hs⟩ := Set.mem_iUnion.1 hxz
    have hrs := prefix_common_vertex_request_eq r s
      ((reservedRawOwnerAttachment r).sourcePrefix.edgeSet_subset_support_prod hr).1
      ((reservedRawOwnerAttachment s).sourcePrefix.edgeSet_subset_support_prod hs).1
    subst s
    exact (Alternating.FinitePath.edgeSet_biUnique
      (reservedRawOwnerAttachment r).sourcePrefix).2 hr hs

theorem reservedRawPrefixEdges_subset_reference : P ⊆ (J).familyEdges := by
  intro e he
  obtain ⟨r, hr⟩ := Set.mem_iUnion.1 he
  exact ⟨(reservedStrongSelectedStartingRecord r).record,
    (reservedStrongSelectedStartingRecord r).record_mem_ladder,
    (reservedRawOwnerAttachment r).sourcePrefix_edges hr⟩

/-- No inserted forward edge enters any one of the restored source owners. -/
theorem reservedRawForward_head_avoids_record (r : Request J S.cut) {e : V × V}
    (he : e ∈ F) : e.2 ∉ (reservedStrongSelectedStartingRecord r).record.support := by
  obtain ⟨s, hs⟩ := Set.mem_iUnion.1 he
  by_cases hrs : r = s
  · subst s
    exact (reservedRawOwnerAttachment r).switchEdges_head_avoids_owner
      (reservedStrongSelectedStartingRecord r).record_mem_ladder (Or.inr hs)
  · exact (reservedRawOwner_forward_other_avoids_record r s hrs hs).2

/-- A forward departure on a starting owner is at that owner's own prefix finish. -/
theorem reservedRawForward_tail_on_record (r : Request J S.cut) {e : V × V}
    (he : e ∈ F) (hx : e.1 ∈ (reservedStrongSelectedStartingRecord r).record.support) :
    e.1 = (reservedRawOwnerAttachment r).anchor := by
  obtain ⟨s, hs⟩ := Set.mem_iUnion.1 he
  by_cases hrs : r = s
  · subst s
    exact (reservedRawOwnerAttachment r).switchEdges_tail_owner_eq_anchor
      (reservedStrongSelectedStartingRecord r).record_mem_ladder (Or.inr hs) hx
  · exact False.elim ((reservedRawOwner_forward_other_avoids_record r s hrs hs).1 hx)

def reservedRawInsertedEdges : Set (V × V) := F ∪ P

/-- The actual simultaneous inserted relation has no branch or merge. -/
theorem reservedRawInsertedEdges_biUnique :
    Relator.BiUnique (fun x y ↦ (x, y) ∈
      reservedRawInsertedEdges (L := L) (hL := hL) (S := S)) := by
  have hF := reservedRawForwardEdges_biUnique (L := L) (hL := hL) (S := S)
  have hP := reservedRawPrefixEdges_biUnique (L := L) (hL := hL) (S := S)
  have hhead : ∀ {x z y}, (x, y) ∈ F → (z, y) ∈ P → False := by
    intro x z y hxy hzy
    obtain ⟨r, hr⟩ := Set.mem_iUnion.1 hzy
    exact reservedRawForward_head_avoids_record r hxy
      ((reservedRawOwnerAttachment r).sourcePrefix_support
        ((reservedRawOwnerAttachment r).sourcePrefix.edgeSet_subset_support_prod hr).2)
  have htail : ∀ {x y z}, (x, y) ∈ F → (x, z) ∈ P → False := by
    intro x y z hxy hxz
    obtain ⟨r, hr⟩ := Set.mem_iUnion.1 hxz
    have hx := reservedRawForward_tail_on_record r hxy
      ((reservedRawOwnerAttachment r).sourcePrefix_support
        ((reservedRawOwnerAttachment r).sourcePrefix.edgeSet_subset_support_prod hr).1)
    have hfinish : x = (reservedRawOwnerAttachment r).sourcePrefix.finish :=
      hx.trans (reservedRawOwnerAttachment r).sourcePrefix_finish.symm
    exact Alternating.FinitePath.no_outgoing_edge_at_finish
      (reservedRawOwnerAttachment r).sourcePrefix z (hfinish ▸ hr)
  constructor
  · intro x z y hxy hzy
    rcases hxy with hxy | hxy <;> rcases hzy with hzy | hzy
    · exact hF.1 hxy hzy
    · exact False.elim (hhead hxy hzy)
    · exact False.elim (hhead hzy hxy)
    · exact hP.1 hxy hzy
  · intro x y z hxy hxz
    rcases hxy with hxy | hxy <;> rcases hxz with hxz | hxz
    · exact hF.2 hxy hxz
    · exact False.elim (htail hxy hxz)
    · exact False.elim (htail hxz hxy)
    · exact hP.2 hxy hxz

#print axioms reservedRawPrefixEdges_biUnique
#print axioms reservedRawInsertedEdges_biUnique

end Erdos599.DWeb.KappaLadder.Deferred
