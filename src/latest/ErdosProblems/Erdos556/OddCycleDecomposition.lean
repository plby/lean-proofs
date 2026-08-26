import ErdosProblems.Erdos556.OddCycleDensity
import ErdosProblems.Erdos556.PieceDecompositionAsymptotic
import ErdosProblems.Erdos556.PieceDensity

/-!
# Bipartite and sparse parts after a small edge deletion

If all odd cycles have length at most `2k`, a sufficiently large graph
of order at most `16k` can be approximated by a bipartite graph and a
vertex-disjoint graph with a hereditary density bound. The error and
order threshold are uniform over all finite graphs.
-/

namespace Erdos556

open SimpleGraph Finset

open scoped Classical in
theorem exists_odd_cycle_decomposition (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ {V : Type*} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ),
      N₀ ≤ Fintype.card V → Fintype.card V ≤ 16 * k →
      (∀ (w : V) (c : G.Walk w w), c.IsCycle → Odd c.length → c.length ≤ 2 * k) →
      ∃ (B F : SimpleGraph V) (S : Finset V),
        B ≤ G ∧ F ≤ G ∧ B.Colorable 2 ∧
        (∀ u v, B.Adj u v → u ∉ S ∧ v ∉ S) ∧
        (∀ u v, F.Adj u v → u ∈ S ∧ v ∈ S) ∧
        (G.edgeFinset.card : ℝ) ≤ B.edgeFinset.card + F.edgeFinset.card +
          ε * (Fintype.card V : ℝ) ^ 2 ∧
        (∀ A : Finset V, ((F.induce (A : Set V)).edgeFinset.card : ℝ) ≤
          ((k : ℝ) + ε * Fintype.card V) * A.card) := by
  obtain ⟨R, hR⟩ := exists_hereditary_density_bound ε hε
  obtain ⟨N₀, hN₀⟩ := exists_uniform_piece_decomposition ε hε R
  refine ⟨N₀, ?_⟩
  intro V _ _ G _ k hN hk ho
  classical
  obtain ⟨P, hP, heP⟩ := hN₀ G hN
  let Q : Finset (Finset V) := P.filter (fun A => (G.induce (A : Set V)).Colorable 2)
  let T : Finset (Finset V) := P.filter (fun A => ¬ (G.induce (A : Set V)).Colorable 2)
  let S : Finset V := T.biUnion id
  let B := pieceGraph G Q
  let F := pieceGraph G T
  have hQsub : Q ⊆ P := filter_subset _ _
  have hTsub : T ⊆ P := filter_subset _ _
  have hQ : (Q : Set (Finset V)).Pairwise Disjoint := hP.1.mono hQsub
  have hT : (T : Set (Finset V)).Pairwise Disjoint := hP.1.mono hTsub
  have hB : B.Colorable 2 := pieceGraph_colorable G Q 2 hQ
    (fun A hA => (mem_filter.mp hA).2)
  have hQT : Disjoint Q T := by
    rw [Finset.disjoint_left]
    intro A hAQ hAT
    exact (mem_filter.mp hAT).2 (mem_filter.mp hAQ).2
  have hQTunion : Q ∪ T = P := filter_union_filter_not_eq _ _
  have heq : B.edgeFinset.card + F.edgeFinset.card =
      ∑ A ∈ P, (G.induce (A : Set V)).edgeFinset.card := by
    rw [pieceGraph_card_edges G Q hQ, pieceGraph_card_edges G T hT,
      ← sum_union hQT, hQTunion]
  refine ⟨B, F, S, pieceGraph_le G Q, pieceGraph_le G T, hB, ?_, ?_, ?_, ?_⟩
  · intro u v huv
    obtain ⟨_, A, hA, hu, hv⟩ := huv
    have hoff (x : V) (hx : x ∈ A) : x ∉ S := by
      intro hxS
      obtain ⟨C, hC, hxC⟩ := mem_biUnion.mp hxS
      have hAC : A ≠ C := by
        intro he
        subst C
        exact Finset.disjoint_left.mp hQT hA hC
      exact Finset.disjoint_left.mp (hP.1 (hQsub hA) (hTsub hC) hAC) hx hxC
    exact ⟨hoff u hu, hoff v hv⟩
  · intro u v huv
    obtain ⟨_, A, hA, hu, hv⟩ := huv
    exact ⟨mem_biUnion.mpr ⟨A, hA, hu⟩, mem_biUnion.mpr ⟨A, hA, hv⟩⟩
  · have heqR : (B.edgeFinset.card : ℝ) + F.edgeFinset.card =
        ∑ A ∈ P, ((G.induce (A : Set V)).edgeFinset.card : ℝ) := by exact_mod_cast heq
    rw [heqR]
    exact heP
  · apply hereditary_density_pieceGraph G T hT
      ((k : ℝ) + ε * Fintype.card V) (by positivity)
    intro A hA
    have hAR : R < A.card := (hP.2 A (hTsub hA)).1
    have hAc : Fintype.card (A : Set V) = A.card := Fintype.card_coe A
    have hAk : Fintype.card (A : Set V) ≤ 16 * k := by
      rw [hAc]
      exact (card_le_univ A).trans hk
    have hoA (w : (A : Set V)) (c : (G.induce (A : Set V)).Walk w w)
        (hc : c.IsCycle) (hcodd : Odd c.length) : c.length ≤ 2 * k := by
      let f : G.induce (A : Set V) ↪g G := SimpleGraph.Embedding.induce (A : Set V)
      have h := ho (f w) (c.map f.toHom) (hc.map f.injective)
        (by simpa only [Walk.length_map] using hcodd)
      simpa only [Walk.length_map] using h
    have hd := hR (G.induce (A : Set V)) k (by omega) hAk
      (hP.2 A (hTsub hA)).2 (mem_filter.mp hA).2 hoA
    apply hereditary_density_of_induce G A
    intro U
    apply (hd U).trans
    gcongr
    rw [hAc]
    exact_mod_cast card_le_univ A

#print axioms exists_odd_cycle_decomposition

end Erdos556
