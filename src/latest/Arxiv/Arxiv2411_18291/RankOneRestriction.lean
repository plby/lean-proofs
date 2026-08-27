import Arxiv.Arxiv2411_18291.GraphEmbeddingPullback
import Arxiv.Arxiv2411_18291.RankOneVertices
import Mathlib.Data.Fintype.EquivFin

/-! # Restricting a rank-one graph to its actual vertices -/

open Finset

noncomputable section

namespace Arxiv2411_18291

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] in
theorem exists_rankOne_embedding (G : Hypergraph V 1) :
    ∃ f : Fin G.card ↪ V, (univ : Finset (Fin G.card)).map f = vertexSupport G ∧
      mapGraph f (complete (Fin G.card) 1) = G := by
  let S := vertexSupport G
  let e : Fin G.card ≃ S := Fintype.equivOfCardEq (by
    simp only [Fintype.card_fin, Fintype.card_coe, S, card_vertexSupport_rankOne])
  let f : Fin G.card ↪ V := e.toEmbedding.trans ⟨Subtype.val, Subtype.val_injective⟩
  have hrange : (univ : Finset (Fin G.card)).map f = S := by
    ext v
    constructor
    · intro hv
      obtain ⟨i, _, rfl⟩ := mem_map.mp hv
      exact (e i).property
    · intro hv
      exact mem_map.mpr ⟨e.symm ⟨v, hv⟩, mem_univ _,
        congrArg Subtype.val (e.apply_symm_apply ⟨v, hv⟩)⟩
  refine ⟨f, hrange, ?_⟩
  have hsub : G ⊆ mapGraph f (complete (Fin G.card) 1) := by
    intro Q hQ
    have hQS : Q.val ⊆ (univ : Finset (Fin G.card)).map f :=
      hrange.symm ▸ subset_vertexSupport hQ
    obtain ⟨s, _, hs⟩ := subset_map_iff.mp hQS
    have hsq : s.card = 1 := by rw [← card_map f, ← hs, Q.property]
    exact (mem_mapGraph _ _ _).mpr ⟨⟨s, hsq⟩, mem_univ _, Subtype.ext hs.symm⟩
  have hcard : (mapGraph f (complete (Fin G.card) 1)).card = G.card := by
    simp only [card_mapGraph, complete, card_univ, Block, Fintype.card_finset_len,
      Fintype.card_fin, Nat.choose_one_right]
  exact (eq_of_subset_of_card_le hsub hcard.le).symm

theorem exists_rankOne_restriction {q : ℕ} (G : Hypergraph V 1) (H : Finset (Block V q))
    (hHG : ∀ Q ∈ H, cliqueEdges 1 Q ⊆ G) :
    ∃ f : Fin G.card ↪ V, ∃ H' : Finset (Block (Fin G.card) q),
      mapGraph f (complete (Fin G.card) 1) = G ∧ mapGraph f H' = H := by
  obtain ⟨f, hrange, hG⟩ := exists_rankOne_embedding G
  obtain ⟨H', hH⟩ := exists_mapGraph_eq_of_supported f H (fun Q hQ =>
    hrange.symm ▸ clique_vertices_subset_rankOne_support (hHG Q hQ))
  exact ⟨f, H', hG, hH⟩

end Arxiv2411_18291
