/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.DeferredGroundingRawPrefixUnion

/-!
# The actual simultaneous raw relation and its degree bounds

Delete the auxiliary cut edges, every selected starting owner, and all raw
backward suffix gadgets. Add the actual forward connectors and restore all
genuine source prefixes. All degree conflicts are discharged from the real
selected paths. No reverse-ray or separator-rooting conclusion is assumed.
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

def reservedRawOwnerEdges : Set (V × V) :=
  ⋃ r : Request J S.cut, (reservedStrongSelectedStartingRecord r).record.edgeSet

def reservedRawBackwardEdges : Set (V × V) :=
  ⋃ r : Request J S.cut, (J).representedEdges (reservedRawOwnerAttachment r).tail

def reservedRawRetainedEdges : Set (V × V) :=
  (((J).familyEdges \ GroundingCut.CE J S.cut) \
    reservedRawOwnerEdges (L := L) (hL := hL) (S := S)) \
      reservedRawBackwardEdges (L := L) (hL := hL) (S := S)

local notation "R" => reservedRawRetainedEdges (L := L) (hL := hL) (S := S)
local notation "N" => reservedRawInsertedEdges (L := L) (hL := hL) (S := S)

/-- The literal simultaneous whole-owner raw switch, retaining all other
unused reference edges and every actual forward and source-prefix insertion. -/
def reservedRawSimultaneousEdges : Set (V × V) := R ∪ N

theorem reservedRawRetained_subset_ownerDeleted (r : Request J S.cut) :
    R ⊆ (J).familyEdges \ (reservedStrongSelectedStartingRecord r).record.edgeSet := by
  intro e he
  exact ⟨he.1.1.1, fun hr ↦ he.1.2 (Set.mem_iUnion.2 ⟨r, hr⟩)⟩

theorem reservedRawRetained_not_backward (r : Request J S.cut) {e : V × V} (he : e ∈ R) :
    e ∉ (J).representedEdges (reservedRawOwnerAttachment r).tail :=
  fun hr ↦ he.2 (Set.mem_iUnion.2 ⟨r, hr⟩)

theorem reservedRawRetained_head_avoids_record (r : Request J S.cut) {e : V × V}
    (he : e ∈ R) : e.2 ∉ (reservedStrongSelectedStartingRecord r).record.support := by
  have hret := reservedRawRetained_subset_ownerDeleted r he
  intro hx
  exact hret.2 ((J).referenceEdge_mem_owner_of_head
    (reservedStrongSelectedStartingRecord r).record_mem_ladder hret.1 hx)

theorem reservedRawRetained_tail_avoids_record (r : Request J S.cut) {e : V × V}
    (he : e ∈ R) : e.1 ∉ (reservedStrongSelectedStartingRecord r).record.support := by
  have hret := reservedRawRetained_subset_ownerDeleted r he
  intro hx
  exact hret.2 ((J).referenceEdge_mem_owner_of_tail
    (reservedStrongSelectedStartingRecord r).record_mem_ladder hret.1 hx)

/-- Every mixed incoming conflict is already absent from the retained reference. -/
theorem reservedRawRetained_inserted_incoming_false {x z y : V}
    (hxy : (x, y) ∈ R) (hzy : (z, y) ∈ N) : False := by
  rcases hzy with hforward | hprefix
  · obtain ⟨r, hr⟩ := Set.mem_iUnion.1 hforward
    exact reservedRawRetained_not_backward r hxy
      ((reservedRawOwnerAttachment r).incoming_reference_represented
        (popularAuxiliary_hasBoundaryIncidence L hL.legal) hr hxy.1.1.1)
  · obtain ⟨r, hr⟩ := Set.mem_iUnion.1 hprefix
    exact reservedRawRetained_head_avoids_record r hxy
      ((reservedRawOwnerAttachment r).sourcePrefix_support
        ((reservedRawOwnerAttachment r).sourcePrefix.edgeSet_subset_support_prod hr).2)

/-- The outgoing counterpart includes all proxy-attachment conflicts. -/
theorem reservedRawRetained_inserted_outgoing_false {x y z : V}
    (hxy : (x, y) ∈ R) (hxz : (x, z) ∈ N) : False := by
  rcases hxz with hforward | hprefix
  · obtain ⟨r, hr⟩ := Set.mem_iUnion.1 hforward
    exact reservedRawRetained_not_backward r hxy
      ((reservedRawOwnerAttachment r).outgoing_ownerDeleted_represented
        (popularAuxiliary_hasBoundaryIncidence L hL.legal)
        (reservedStrongSelectedStartingRecord r).record_mem_ladder hr
        (reservedRawRetained_subset_ownerDeleted r hxy))
  · obtain ⟨r, hr⟩ := Set.mem_iUnion.1 hprefix
    exact reservedRawRetained_tail_avoids_record r hxy
      ((reservedRawOwnerAttachment r).sourcePrefix_support
        ((reservedRawOwnerAttachment r).sourcePrefix.edgeSet_subset_support_prod hr).1)

/-- The actual global raw edge relation has indegree and outdegree at most one. -/
theorem reservedRawSimultaneousEdges_biUnique :
    Relator.BiUnique (fun x y ↦ (x, y) ∈
      reservedRawSimultaneousEdges (L := L) (hL := hL) (S := S)) := by
  have hR : Relator.BiUnique (fun x y ↦ (x, y) ∈ R) :=
    ⟨fun _ _ _ h₁ h₂ ↦ (J).raw_familyEdges_biUnique.1 h₁.1.1.1 h₂.1.1.1,
      fun _ _ _ h₁ h₂ ↦ (J).raw_familyEdges_biUnique.2 h₁.1.1.1 h₂.1.1.1⟩
  have hN := reservedRawInsertedEdges_biUnique (L := L) (hL := hL) (S := S)
  constructor
  · intro x z y hxy hzy
    rcases hxy with hxy | hxy <;> rcases hzy with hzy | hzy
    · exact hR.1 hxy hzy
    · exact False.elim (reservedRawRetained_inserted_incoming_false hxy hzy)
    · exact False.elim (reservedRawRetained_inserted_incoming_false hzy hxy)
    · exact hN.1 hxy hzy
  · intro x y z hxy hxz
    rcases hxy with hxy | hxy <;> rcases hxz with hxz | hxz
    · exact hR.2 hxy hxz
    · exact False.elim (reservedRawRetained_inserted_outgoing_false hxy hxz)
    · exact False.elim (reservedRawRetained_inserted_outgoing_false hxz hxy)
    · exact hN.2 hxy hxz

theorem reservedRawRetained_disjoint_inserted : Disjoint R N := by
  apply Set.disjoint_left.2
  intro e heR heN
  exact reservedRawRetained_inserted_incoming_false heR heN

theorem reservedRawSimultaneousEdges_subset_adj :
    reservedRawSimultaneousEdges (L := L) (hL := hL) (S := S) ⊆
      {e | Gamma.graph.Adj e.1 e.2} := by
  intro e he
  rcases he with hretained | hforward | hprefix
  · obtain ⟨q, _hq, heq⟩ := hretained.1.1.1
    exact q.edgeSet_subset_adj heq
  · obtain ⟨r, hr⟩ := Set.mem_iUnion.1 hforward
    exact (reservedRawOwnerAttachment r).sourceEdges_subset_adj (Or.inl (Or.inr hr))
  · obtain ⟨r, hr⟩ := Set.mem_iUnion.1 hprefix
    exact (reservedRawOwnerAttachment r).sourcePrefix.edgeSet_subset_adj hr

theorem reservedRawSimultaneousEdges_contains_forward (r : Request J S.cut) :
    (reservedRawOwnerAttachment r).forwardEdges ⊆
      reservedRawSimultaneousEdges (L := L) (hL := hL) (S := S) :=
  fun _ he ↦ Or.inr (Or.inl (Set.mem_iUnion.2 ⟨r, he⟩))

theorem reservedRawSimultaneousEdges_contains_prefix (r : Request J S.cut) :
    (reservedRawOwnerAttachment r).sourcePrefix.edgeSet ⊆
      reservedRawSimultaneousEdges (L := L) (hL := hL) (S := S) :=
  fun _ he ↦ Or.inr (Or.inr (Set.mem_iUnion.2 ⟨r, he⟩))

#print axioms reservedRawSimultaneousEdges_biUnique
#print axioms reservedRawSimultaneousEdges_subset_adj

end Erdos599.DWeb.KappaLadder.Deferred
