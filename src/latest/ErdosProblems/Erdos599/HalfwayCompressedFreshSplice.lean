/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayFreshIncidence

/-!
# Extracting the genuinely fresh part of an occurrence splice

The occurrence-aware whole-family transaction already supplies one sound
classified relation containing all current edges.  Its genuinely new part is
therefore the set difference by the current edge set.  If the construction
proves that this difference has no edge entering the old carrier, all local
compatibility fields of `FreshAdvanceSpliceRelation` follow formally.

This conversion does not project split-web paths and does not postulate a
second relation: the union of the old relation and the extracted fresh part
is proved equal to the original occurrence relation.
-/

noncomputable section

open Cardinal Set

namespace Erdos599.Blueprint.LinkageBlueprint

open DirectedPath Alternating

universe u

variable {V : Type u}
variable {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}

namespace CompressedWholeFamilyAdvanceSpliceRelation

variable {ancestor current : LinkageBlueprint Gamma Y kappa}
variable {Zf : FracturedWarp Gamma}
variable {A : CompressedFracturedAssignment Zf Y}
variable {z : V} {T Z persistent B : Set V}

/-- The occurrence relation is exactly the old edge relation together with
its set-theoretically fresh part. -/
theorem current_union_fresh_eq
    (C : CompressedWholeFamilyAdvanceSpliceRelation
      ancestor current A z T Z persistent B) :
    current.edgeSet ∪ (C.splice.edge \ current.edgeSet) = C.splice.edge := by
  apply Set.Subset.antisymm
  · rintro e (he | he)
    · exact C.old_edges he
    · exact he.1
  · intro e he
    by_cases heold : e ∈ current.edgeSet
    · exact Or.inl heold
    · exact Or.inr ⟨he, heold⟩

/-- Extract the fresh relation from a classified occurrence transaction.

The sole additional input is the literal incidence theorem proved by the
club-stage construction: a genuinely new edge never enters an old carrier
vertex. -/
def toFreshOfNoIncomingOld
    (C : CompressedWholeFamilyAdvanceSpliceRelation
      ancestor current A z T Z persistent B)
    (hinfinite : ∀ s, A.outcome s = none →
      IsPopular Gamma Y persistent kappa s.1)
    (hnoIncoming : ∀ {x y : V}, x ∈ current.vertexSet →
      (y, x) ∈ C.splice.edge \ current.edgeSet → False) :
    FreshAdvanceSpliceRelation ancestor current z T Z persistent B where
  fresh := C.splice.edge \ current.edgeSet
  carrier := C.splice.carrier
  current_vertices := C.old_vertices
  fresh_edge_in_graph := fun _ he ↦ C.splice.edge_in_graph he.1
  fresh_endpoints_mem := fun e he ↦ C.splice.endpoints_mem e he.1
  fresh_disjoint :=
    FreshIncidence.disjoint_old_of_noIncomingOld current _ hnoIncoming
  union_biunique := by
    rw [C.current_union_fresh_eq]
    exact C.splice.biunique
  no_forward_sandwich :=
    FreshIncidence.noForwardSandwich_of_noIncomingOld current _ hnoIncoming
  fresh_no_directed_cycle := by
    rintro ⟨cycle, hcycle⟩
    exact C.splice.no_directed_cycle
      ⟨cycle, hcycle.trans Set.sdiff_subset⟩
  fresh_no_reverse_ray := by
    rintro ⟨ray, hray⟩
    exact C.splice.no_reverse_ray
      ⟨ray, fun n ↦ Set.sdiff_subset (hray n)⟩
  fresh_no_incoming_old_real :=
    FreshIncidence.noIncomingOldReal_of_noIncomingOld
      current _ hnoIncoming
  sink_boundary := by
    rw [C.current_union_fresh_eq]
    intro x hx
    rcases C.splice.sink_boundary hx with hxInfinite | hxT
    · exact Or.inl (A.infiniteSources_popular hinfinite hxInfinite)
    · exact Or.inr hxT
  vertices_roofed := C.splice.vertices_roofed
  covers_source := by
    rw [C.current_union_fresh_eq]
    exact C.splice.covers_source
  vertices_closed := C.splice.vertices_closed
  card_carrier := C.splice.card_carrier
  every_relation_ray_strong := by
    rw [C.current_union_fresh_eq]
    exact C.splice.every_relation_ray_strong
  stable_boundary := by
    rw [C.current_union_fresh_eq]
    exact C.splice.stable_boundary
  target_path := C.splice.target_path
  target_path_start := C.splice.target_path_start
  target_path_finish := C.splice.target_path_finish
  target_path_vertices := C.splice.target_path_vertices
  target_path_edges := by
    rw [C.current_union_fresh_eq]
    exact C.splice.target_path_edges
  preserves_other_real_terminals := by
    rw [C.current_union_fresh_eq]
    exact C.splice.preserves_other_real_terminals
  persistent_boundary := by
    rw [C.current_union_fresh_eq]
    exact C.persistent_boundary
  inherited_boundary := by
    intro x hxAncestor hxCurrent hxz
    rw [C.current_union_fresh_eq]
    exact C.inherited_boundary x hxAncestor hxCurrent hxz

/-- Retain the occurrence endpoint provenance after extracting the fresh
part.  This is the exact object consumed by the occurrence-aware scheduled
request in `GlobalAdvance931`. -/
def toCompressedFreshOfNoIncomingOld
    (C : CompressedWholeFamilyAdvanceSpliceRelation
      ancestor current A z T Z persistent B)
    (hinfinite : ∀ s, A.outcome s = none →
      IsPopular Gamma Y persistent kappa s.1)
    (hnoIncoming : ∀ {x y : V}, x ∈ current.vertexSet →
      (y, x) ∈ C.splice.edge \ current.edgeSet → False) :
    CompressedFreshAdvanceSpliceRelation
      ancestor current A z T Z persistent B where
  attachment := C.toFreshOfNoIncomingOld hinfinite hnoIncoming
  assigned_edges := by
    change A.finiteEdges ⊆
      current.edgeSet ∪ (C.splice.edge \ current.edgeSet)
    rw [C.current_union_fresh_eq]
    exact C.splice.assigned_edges
  infinite_sources_sink := by
    change A.infiniteSources ⊆
      {x | x ∈ C.splice.carrier ∧
        ¬ ∃ y, (x, y) ∈
          current.edgeSet ∪ (C.splice.edge \ current.edgeSet)}
    rw [C.current_union_fresh_eq]
    exact C.splice.infinite_sources_sink

#print axioms current_union_fresh_eq
#print axioms toFreshOfNoIncomingOld
#print axioms toCompressedFreshOfNoIncomingOld

end CompressedWholeFamilyAdvanceSpliceRelation
end Erdos599.Blueprint.LinkageBlueprint
