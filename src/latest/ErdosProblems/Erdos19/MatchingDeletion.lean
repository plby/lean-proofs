import ErdosProblems.Erdos19.GraphMatching
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges

/-! # A matching consumes at most one reservoir edge at each vertex -/

namespace Erdos19

open Finset
open _root_.SimpleGraph

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] [DecidableEq V] {G : _root_.SimpleGraph V}

theorem matching_spanning_degree_le_one (M : G.Subgraph) (hM : M.IsMatching) (v : V) :
    M.spanningCoe.degree v ≤ 1 := by
  classical
  rw [_root_.SimpleGraph.degree]
  apply card_le_one.mpr
  intro x hx y hy
  exact hM.eq_of_adj_left
    (by simpa only [mem_neighborFinset, Subgraph.spanningCoe_adj] using hx)
    (by simpa only [mem_neighborFinset, Subgraph.spanningCoe_adj] using hy)

theorem matching_cut_card_le (M : G.Subgraph) (hM : M.IsMatching)
    (A B : Finset V) (hAB : Disjoint A B) :
    (M.spanningCoe.between (A : Set V) (B : Set V)).edgeFinset.card ≤ A.card := by
  classical
  let C := M.spanningCoe.between (A : Set V) (B : Set V)
  have hC : C.IsBipartiteWith (A : Set V) (B : Set V) :=
    M.spanningCoe.between_isBipartiteWith (Finset.disjoint_coe.mpr hAB)
  calc
    C.edgeFinset.card = ∑ v ∈ A, C.degree v :=
      (C.isBipartiteWith_sum_degrees_eq_card_edges hC).symm
    _ ≤ ∑ _v ∈ A, 1 := by
      apply sum_le_sum
      intro v _
      exact (C.degree_le_of_le between_le).trans (matching_spanning_degree_le_one M hM v)
    _ = A.card := by simp

theorem degree_le_delete_matching_add_one (R : _root_.SimpleGraph V)
    (M : G.Subgraph) (hM : M.IsMatching) (v : V) :
    R.degree v ≤ (R.deleteEdges M.edgeSet).degree v + 1 := by
  classical
  let Q := R.deleteEdges M.edgeSet
  have hsub : R.neighborFinset v ⊆ Q.neighborFinset v ∪ M.spanningCoe.neighborFinset v := by
    intro w hw
    have hr : R.Adj v w := by simpa only [mem_neighborFinset] using hw
    by_cases hm : M.Adj v w
    · apply mem_union_right
      simpa only [mem_neighborFinset, Subgraph.spanningCoe_adj] using hm
    · apply mem_union_left
      have hq : Q.Adj v w := deleteEdges_adj.mpr ⟨hr, fun h ↦ hm (Subgraph.mem_edgeSet.mp h)⟩
      simpa only [mem_neighborFinset] using hq
  have hb : R.degree v ≤ Q.degree v + M.spanningCoe.degree v := by
    have h := (card_le_card hsub).trans (card_union_le _ _)
    simpa only [card_neighborFinset_eq_degree] using h
  exact hb.trans (Nat.add_le_add_left (matching_spanning_degree_le_one M hM v) _)

theorem delete_matching_has_cross_edge (R : _root_.SimpleGraph V)
    (M : G.Subgraph) (hM : M.IsMatching) (A B : Finset V) (hAB : Disjoint A B)
    (hcut : A.card < (R.between (A : Set V) (B : Set V)).edgeFinset.card) :
    ∃ x ∈ A, ∃ y ∈ B, (R.deleteEdges M.edgeSet).Adj x y := by
  classical
  by_contra hnone
  push Not at hnone
  have hle : R.between (A : Set V) (B : Set V) ≤
      M.spanningCoe.between (A : Set V) (B : Set V) := by
    intro x y hxy
    refine ⟨?_, hxy.2⟩
    by_contra hnot
    have hq : (R.deleteEdges M.edgeSet).Adj x y :=
      deleteEdges_adj.mpr ⟨hxy.1, fun h ↦ hnot (Subgraph.mem_edgeSet.mp h)⟩
    rcases hxy.2 with h | h
    · exact hnone x h.1 y h.2 hq
    · exact hnone y h.2 x h.1 hq.symm
  have hcard := card_le_card (edgeFinset_mono hle)
  have hsmall := matching_cut_card_le M hM A B hAB
  omega

#print axioms degree_le_delete_matching_add_one
#print axioms delete_matching_has_cross_edge

end Erdos19
