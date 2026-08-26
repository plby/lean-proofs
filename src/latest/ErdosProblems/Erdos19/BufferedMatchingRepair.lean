import ErdosProblems.Erdos19.TrimmedMatching
import ErdosProblems.Erdos19.SubgraphLift

/-! # A matching repair with bounded prior edge use

Every repair edge meets a vertex requiring coverage. Its total vertex
footprint is consequently at most twice the number of such vertices.
-/

namespace Erdos19

open _root_.SimpleGraph

variable {V : Type*} [Fintype V]

theorem missing_neighbors_after_edge_use (G used : _root_.SimpleGraph V)
    (X : Set V) (v : V) :
    (X \ (G \ used).neighborSet v).ncard ≤
      (X \ G.neighborSet v).ncard + (used.neighborSet v).ncard := by
  have hsub : X \ (G \ used).neighborSet v ⊆
      (X \ G.neighborSet v) ∪ used.neighborSet v := by
    intro w hw
    by_cases hG : G.Adj v w
    · right
      by_contra hused
      exact hw.2 ⟨hG, hused⟩
    · exact Or.inl ⟨hw.1, hG⟩
  exact (Set.ncard_le_ncard hsub).trans (Set.ncard_union_le _ _)

theorem exists_buffered_matching_repair (G used : _root_.SimpleGraph V)
    (A B : Set V) (missing load : ℕ) (hAB : Disjoint A B)
    (hB : missing + load ≤ B.ncard)
    (hmissing : ∀ u ∈ A, ((A ∪ B) \ G.neighborSet u).ncard ≤ missing)
    (hload : ∀ u ∈ A, (used.neighborSet u).ncard ≤ load) :
    ∃ M : G.Subgraph, M.IsMatching ∧ A ⊆ M.verts ∧ M.verts ⊆ A ∪ B ∧
      M.verts.ncard ≤ 2 * A.ncard ∧ Disjoint used M.spanningCoe ∧
      ∀ u v, M.Adj u v → u ∈ A ∨ v ∈ A := by
  let Q := G \ used
  have hQmissing : ∀ u ∈ A, ((A ∪ B) \ Q.neighborSet u).ncard ≤ missing + load := by
    intro u hu
    exact (missing_neighbors_after_edge_use G used (A ∪ B) u).trans
      (Nat.add_le_add (hmissing u hu) (hload u hu))
  obtain ⟨M, hM, hcover, hverts, hmeet⟩ :=
    exists_matching_covering_with_buffer Q A B (missing + load) hAB hB hQmissing
  have hQG : Q ≤ G := sdiff_le
  let N := liftSubgraph hQG M
  refine ⟨N, hM, hcover, hverts, matching_verts_ncard_le_of_edges_meet M hM A hmeet, ?_, hmeet⟩
  apply _root_.SimpleGraph.disjoint_left.mpr
  intro u v huv hMuv
  have hQ : Q.Adj u v := M.adj_sub hMuv
  exact hQ.2 huv

#print axioms exists_buffered_matching_repair

end Erdos19
