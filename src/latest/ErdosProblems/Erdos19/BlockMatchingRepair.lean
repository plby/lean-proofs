import ErdosProblems.Erdos19.BufferedMatchingRepair

/-! # Combining independent repairs in disjoint blocks -/

namespace Erdos19

open _root_.SimpleGraph

variable {V I : Type*} [Fintype V]

theorem exists_disjoint_block_matching_repair (G used : _root_.SimpleGraph V)
    (A B : I → Set V) (missing load : ℕ)
    (hblocks : Pairwise fun i j ↦ Disjoint (A i ∪ B i) (A j ∪ B j))
    (hAB : ∀ i, Disjoint (A i) (B i))
    (hbuffer : ∀ i, missing + load ≤ (B i).ncard)
    (hmissing : ∀ i u, u ∈ A i → ((A i ∪ B i) \ G.neighborSet u).ncard ≤ missing)
    (hload : ∀ i u, u ∈ A i → (used.neighborSet u).ncard ≤ load) :
    ∃ M : G.Subgraph, M.IsMatching ∧ (⋃ i, A i) ⊆ M.verts ∧
      M.verts ⊆ ⋃ i, A i ∪ B i ∧
      M.verts.ncard ≤ 2 * (⋃ i, A i).ncard ∧ Disjoint used M.spanningCoe ∧
      ∀ u v, M.Adj u v → u ∈ (⋃ i, A i) ∨ v ∈ (⋃ i, A i) := by
  classical
  have hex (i : I) := exists_buffered_matching_repair G used (A i) (B i) missing load
    (hAB i) (hbuffer i) (hmissing i) (hload i)
  choose M hM hcover hverts hcard hdis hmeet using hex
  let N := ⨆ i, M i
  have hN : N.IsMatching := by
    apply Subgraph.IsMatching.iSup hM
    intro i j hij
    exact (hblocks hij).mono
      ((M i).support_subset_verts.trans (hverts i))
      ((M j).support_subset_verts.trans (hverts j))
  have hNmeet : ∀ u v, N.Adj u v → u ∈ (⋃ i, A i) ∨ v ∈ (⋃ i, A i) := by
    intro u v huv
    obtain ⟨i, hi⟩ := Subgraph.iSup_adj.mp huv
    exact (hmeet i u v hi).elim
      (fun h ↦ Or.inl (Set.mem_iUnion.mpr ⟨i, h⟩))
      (fun h ↦ Or.inr (Set.mem_iUnion.mpr ⟨i, h⟩))
  refine ⟨N, hN, ?_, ?_, matching_verts_ncard_le_of_edges_meet N hN _ hNmeet, ?_, hNmeet⟩
  · intro v hv
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hv
    rw [show N.verts = ⋃ i, (M i).verts from Subgraph.verts_iSup]
    exact Set.mem_iUnion.mpr ⟨i, hcover i hi⟩
  · intro v hv
    rw [show N.verts = ⋃ i, (M i).verts from Subgraph.verts_iSup] at hv
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hv
    exact Set.mem_iUnion.mpr ⟨i, hverts i hi⟩
  · apply _root_.SimpleGraph.disjoint_left.mpr
    intro u v huv hNuv
    obtain ⟨i, hi⟩ := Subgraph.iSup_adj.mp hNuv
    exact _root_.SimpleGraph.disjoint_left.mp (hdis i) u v huv hi

#print axioms exists_disjoint_block_matching_repair

end Erdos19
