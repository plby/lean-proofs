import ErdosProblems.Erdos19.GraphMatching

/-! # A perfect matching on a prescribed even vertex set -/

namespace Erdos19

open _root_.SimpleGraph

theorem exists_matching_on_even_set_of_dense_induced
    {V : Type*} [Fintype V] (G : _root_.SimpleGraph V) (A : Set V)
    (heven : Even A.ncard)
    (hdegree : ∀ v ∈ A, A.ncard ≤ 2 * (A ∩ G.neighborSet v).ncard) :
    ∃ M : G.Subgraph, M.IsMatching ∧ M.verts = A := by
  classical
  let _ : Fintype A := Fintype.ofFinite A
  have hneighbors (v : A) : ((G.induce A).neighborSet v).ncard =
      (A ∩ G.neighborSet v.1).ncard := by
    let e : (G.induce A).neighborSet v ≃ ↥(A ∩ G.neighborSet v.1) :=
      { toFun := fun y ↦ ⟨y.1.1, y.1.2, y.2⟩
        invFun := fun y ↦ ⟨⟨y.1, y.2.1⟩, y.2.2⟩
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl }
    simpa only [Set.fintypeCard_eq_ncard] using Fintype.card_congr e
  obtain ⟨M, hM⟩ := exists_perfectMatching_of_two_mul_neighbor_ncard_ge (G.induce A)
    (by simpa only [Set.fintypeCard_eq_ncard] using heven) (fun v ↦ by
      rw [hneighbors, Set.fintypeCard_eq_ncard]
      exact hdegree v.1 v.2)
  let emb : G.induce A ↪g G := _root_.SimpleGraph.Embedding.induce A
  refine ⟨M.map emb.toHom, hM.1.map emb.toHom emb.injective, ?_⟩
  have hMv : M.verts = Set.univ := Set.eq_univ_of_forall hM.2
  rw [Subgraph.map_verts, hMv]
  ext v
  constructor
  · rintro ⟨w, _, rfl⟩
    exact w.2
  · intro hv
    exact ⟨⟨v, hv⟩, Set.mem_univ _, rfl⟩

#print axioms exists_matching_on_even_set_of_dense_induced

end Erdos19
