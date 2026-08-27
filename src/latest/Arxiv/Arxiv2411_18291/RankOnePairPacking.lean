import Arxiv.Arxiv2411_18291.PairMatchingCounts
import Arxiv.Arxiv2411_18291.RankOneVertices

/-! # A finite rank-one packing estimate for pairs -/

open Finset

noncomputable section

namespace Arxiv2411_18291

theorem exists_rankOne_pair_packing_leave_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : Hypergraph V 1) (H : Finset (Block V 2))
    (hHG : ∀ Q ∈ H, cliqueEdges 1 Q ⊆ G) (δ : ℝ)
    (hdegree : ∀ e ∈ G, δ ≤ ((H.filter fun Q => e.val ⊆ Q.val).card : ℝ)) :
    ∃ D : Finset (Block V 2), D ⊆ H ∧ IsDecomposition (cliqueSupport 1 D) D ∧
      ((G \ cliqueSupport 1 D).card : ℝ) ≤ max 1 ((G.card : ℝ) - 2 * δ) := by
  have hHS : ∀ Q ∈ H, Q.val ⊆ vertexSupport G :=
    fun Q hQ => clique_vertices_subset_rankOne_support (hHG Q hQ)
  have hvertices : ∀ u ∈ vertexSupport G,
      δ ≤ ((H.filter fun Q => u ∈ Q.val).card : ℝ) := by
    intro u hu
    obtain ⟨e, he, hue⟩ := mem_biUnion.mp hu
    have hs := one_block_eq_singleton hue
    simpa only [hs, singleton_subset_iff] using hdegree e he
  obtain ⟨D, hDH, hD, hbound⟩ := exists_pair_packing_leave_bound (vertexSupport G) H hHS δ hvertices
  have hcard : (G \ cliqueSupport 1 D).card = (vertexSupport G \ vertexSupport D).card := by
    rw [← card_vertexSupport_rankOne (G \ cliqueSupport 1 D),
      vertexSupport_sdiff_rankOne, vertexSupport_cliqueSupport_one]
  refine ⟨D, hDH, hD.isDecomposition_rankOne, ?_⟩
  rw [hcard]
  simpa only [card_vertexSupport_rankOne] using hbound

end Arxiv2411_18291
