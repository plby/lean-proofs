import Arxiv.Arxiv2411_18291.ExchangeElimination
import Arxiv.Arxiv2411_18291.PairRootEmbedding

/-!
# A finite pattern for cancelling an opposite-sign pair

The strengthened exchange construction supplies the designated pair,
its common edge, admissibility, and the intersection bound. The union
of the two root cliques has no additional induced pattern edges.
Every target pair with the same intersection has a valid root map.
-/

open Finset

noncomputable section

namespace Arxiv2411_18291

variable {W : Type*} [Fintype W] [DecidableEq W] {q r : ℕ}

structure IsEliminationPair (S : ExchangeSystem W q (r + 1)) (N : Block W q)
    (e : Block W (r + 1)) : Prop where
  negative_mem : N ∈ S.negative
  vertex_inter : S.base.val ∩ N.val = e.val
  locality : ∀ f ∈ S.graph, f.val ∩ (S.base.val ∪ N.val) ⊆ S.base.val ∨
    f.val ∩ (S.base.val ∪ N.val) ⊆ N.val
  cross_simple : IsCrossSimple (r + 1) S.positive S.negative

theorem IsEliminationPair.admissible {S : ExchangeSystem W q (r + 1)}
    {N : Block W q} {e : Block W (r + 1)} (h : IsEliminationPair S N e) (hqr : r + 1 ≤ q) :
    IsAdmissible S.graph (S.base.val ∪ N.val) := by
  intro f hf _
  have hc : (f.val ∩ (S.base.val ∪ N.val)).card ≤ r + 1 := by
    simpa only [f.property] using card_le_card
      (inter_subset_left (s₁ := f.val) (s₂ := S.base.val ∪ N.val))
  rcases h.locality f hf with hp | hn
  · obtain ⟨s, hs, hsP, hsr⟩ := exists_subsuperset_card_eq hp hc
      (by simpa only [S.base.property] using hqr)
    exact ⟨⟨s, hsr⟩, S.positive_decomposition.clique_subset S.base_mem
      ((mem_cliqueEdges _ _).mpr hsP), hsP.trans subset_union_left, hs⟩
  · obtain ⟨s, hs, hsN, hsr⟩ := exists_subsuperset_card_eq hn hc
      (by simpa only [N.property] using hqr)
    exact ⟨⟨s, hsr⟩, S.negative_decomposition.clique_subset h.negative_mem
      ((mem_cliqueEdges _ _).mpr hsN), hsN.trans subset_union_right, hs⟩

theorem IsEliminationPair.new_edges {S : ExchangeSystem W q (r + 1)}
    {N : Block W q} {e : Block W (r + 1)} (h : IsEliminationPair S N e) :
    newEdges (S.base.val ∪ N.val) S.graph =
      S.graph \ (cliqueEdges (r + 1) S.base ∪ cliqueEdges (r + 1) N) := by
  ext f
  rw [mem_newEdges, mem_sdiff, mem_union]
  constructor
  · rintro ⟨hf, hn⟩
    refine ⟨hf, ?_⟩
    rintro (hp | hm)
    · exact hn (((mem_cliqueEdges _ _).mp hp).trans subset_union_left)
    · exact hn (((mem_cliqueEdges _ _).mp hm).trans subset_union_right)
  · rintro ⟨hf, hn⟩
    refine ⟨hf, ?_⟩
    intro hsub
    have hinter : f.val ∩ (S.base.val ∪ N.val) = f.val := inter_eq_left.mpr hsub
    rcases h.locality f hf with hp | hm
    · exact hn (Or.inl ((mem_cliqueEdges _ _).mpr (hinter ▸ hp)))
    · exact hn (Or.inr ((mem_cliqueEdges _ _).mpr (hinter ▸ hm)))

theorem exists_elimination_pattern (q r : ℕ) (hqr : r + 1 < q) :
    ∃ T : FiniteExchangeSystem q (r + 1), ∃ N : Block T.Vertex q,
      ∃ e : Block T.Vertex (r + 1), IsEliminationPair T.system N e ∧
        T.system.graph.card ≤ 3 * (2 * q) ^ (r + 1) * (q.choose (r + 1)) ^ 2 := by
  obtain ⟨T, A, hcard, hA, hcross⟩ :=
    exists_crossSimple_clique_exchange q (r + 1) (Nat.succ_pos r) hqr
  obtain ⟨e, he⟩ := cliqueEdges_nonempty hqr.le T.system.base
  obtain ⟨N, hN, hNe⟩ := hA.2.2.1 e he
  refine ⟨T, N, e, ⟨hA.1 hN, ?_, fun f hf => hA.pair_local hN hf, hcross⟩, hcard⟩
  rw [inter_comm]
  exact vertices_inter_eq_of_cliqueEdges_singleton (Nat.succ_pos r) N T.system.base e hNe

variable {V : Type*} [DecidableEq V]

theorem IsEliminationPair.root_map {S : ExchangeSystem W q (r + 1)}
    {N : Block W q} {e : Block W (r + 1)} (h : IsEliminationPair S N e)
    (P Q : Block V q) (d : Block V (r + 1)) (hPQ : P.val ∩ Q.val = d.val) :
    ∃ φ : ↥(S.base.val ∪ N.val) ↪ V,
      rootImage φ S.base subset_union_left = P ∧ rootImage φ N subset_union_right = Q :=
  exists_pair_root_map S.base N e h.vertex_inter P Q d hPQ

omit [Fintype W] [DecidableEq V] in
theorem pair_extension_roots {P₀ N₀ : Block W q} {P N : Block V q}
    (φ : ↥(P₀.val ∪ N₀.val) ↪ V) (hP : rootImage φ P₀ subset_union_left = P)
    (hN : rootImage φ N₀ subset_union_right = N) (f : EmbeddingExtension φ) :
    mapBlock f.val P₀ = P ∧ mapBlock f.val N₀ = N :=
  ⟨(f.map_rootBlock φ P₀ subset_union_left).trans hP,
    (f.map_rootBlock φ N₀ subset_union_right).trans hN⟩

end Arxiv2411_18291
