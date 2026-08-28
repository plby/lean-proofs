import ErdosProblems.Erdos577.FullLeafHeavyAdjacentLabels

/-! Actual two-block partitions and exact remainders for the adjacent first-row argument. -/

namespace Erdos577.FullLeafHeavy

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

omit [DecidableEq V] in
lemma neighbor_edge_of_clique {t : Finset V} (hcl : G.IsClique t) {z : V}
    (htwo : 2 ≤ degreeIn G z t) :
    ∃ u ∈ t, ∃ v ∈ t, G.Adj z u ∧ G.Adj z v ∧ G.Adj u v := by
  obtain ⟨u, hu, v, hv, huv⟩ := one_lt_card.mp (show 1 < (t.filter (G.Adj z)).card by
    change 1 < degreeIn G z t
    omega)
  obtain ⟨hut, hzu⟩ := mem_filter.mp hu
  obtain ⟨hvt, hzv⟩ := mem_filter.mp hv
  exact ⟨u, hut, v, hvt, hzu, hzv, hcl hut hvt huv⟩

lemma partition_of_core_split {core t : Finset V} {z : V} (ht : t ⊆ core)
    (hz : z ∉ core) (hfirst : QuadOn G (insert z t)) (hsecond : G.IsNClique 4 (core \ t)) :
    ∃ f : BlockPartition G (insert z core),
      f.weightSum (edgeCount G) = edgeCount G (insert z t) + 6 := by
  have hdis : Disjoint (insert z t) (core \ t) := disjoint_insert_left.mpr
    ⟨fun hh ↦ hz (mem_sdiff.mp hh).1, disjoint_sdiff_self_right⟩
  let f := (BlockPartition.single hfirst).union
    (BlockPartition.single (QuadOn.of_clique hsecond.card_eq hsecond.isClique)) hdis
  have he : (insert z t) ∪ (core \ t) = insert z core := by
    rw [insert_union, union_sdiff_of_subset ht]
  have hw : f.weightSum (edgeCount G) = edgeCount G (insert z t) + 6 := by
    rw [BlockPartition.weightSum_union, BlockPartition.weightSum_single,
      BlockPartition.weightSum_single, edgeCount_clique hsecond.isClique, hsecond.card_eq]
    rfl
  let all : BlockPartition G (insert z core) := {
    blocks := f.blocks
    disjoint := f.disjoint
    cover := f.cover.trans he
    quad := f.quad }
  exact ⟨all, hw⟩

omit [DecidableRel G.Adj] in
lemma adjacent_matching_remainder (q : Quadrilateral G) {x : V} (hx : x ∉ q.support)
    (h1 : G.Adj x (q 1)) :
    ∃ m : TwoEdges G, m.support = insert x (q.support.erase (q 0)) := by
  have hout (i : Fin 4) : x ≠ q i := fun he ↦ hx (he ▸ (q.mem_support _).mpr ⟨i, rfl⟩)
  let m : TwoEdges G := {
    vertices := fourTuple x (q 1) (q 2) (q 3) (hout 1) (hout 2) (hout 3)
      (q.injective.ne (by decide : (1 : Fin 4) ≠ 2))
      (q.injective.ne (by decide : (1 : Fin 4) ≠ 3))
      (q.injective.ne (by decide : (2 : Fin 4) ≠ 3))
    firstEdge := h1
    secondEdge := q.adjacent 2 }
  refine ⟨m, ?_⟩
  rw [TwoEdges.support, fourTuple_support, FullRow.erase_zero_support]

omit [DecidableRel G.Adj] in
lemma adjacent_triangle_remainder (q : Quadrilateral G) {x : V}
    (h0 : G.Adj x (q 0)) (h1 : G.Adj x (q 1)) :
    TriangleIn G (insert x (q.support.erase (q 2))) := by
  refine ⟨{x, q 0, q 1}, ?_, SimpleGraph.is3Clique_triple_iff.mpr ⟨h0, h1, q.adjacent 0⟩⟩
  refine insert_subset (mem_insert_self _ _) (insert_subset ?_ (singleton_subset_iff.mpr ?_))
  · exact mem_insert_of_mem (mem_erase.mpr
      ⟨q.injective.ne (by decide : (0 : Fin 4) ≠ 2), (q.mem_support _).mpr ⟨0, rfl⟩⟩)
  · exact mem_insert_of_mem (mem_erase.mpr
      ⟨q.injective.ne (by decide : (1 : Fin 4) ≠ 2), (q.mem_support _).mpr ⟨1, rfl⟩⟩)

end Erdos577.FullLeafHeavy
