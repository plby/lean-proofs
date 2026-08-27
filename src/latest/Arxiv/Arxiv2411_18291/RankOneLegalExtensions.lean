import Arxiv.Arxiv2411_18291.VertexAvoidingExtensions
import Arxiv.Arxiv2411_18291.RankOneVertices
import Arxiv.Arxiv2411_18291.LegalEmbeddingCount

/-! # Deterministic availability for rank-one greedy extensions -/

open Finset

noncomputable section

namespace Arxiv2411_18291

variable {W V : Type*} [Fintype W] [Fintype V] [DecidableEq W] [DecidableEq V]
variable {F : Finset W}

omit [DecidableEq W] [DecidableEq V] in
theorem exists_vertex_avoiding_extension (φ : F ↪ V) (U : Finset V)
    (hn : Fintype.card W + U.card ≤ Fintype.card V) :
    ∃ f : EmbeddingExtension φ, ∀ x, x ∉ F → f.val x ∉ U := by
  classical
  let T : Finset V := univ \ (usedVertices φ ∪ U)
  have hc : Fintype.card (FreeVertices F) ≤ T.card := by
    rw [show Fintype.card (FreeVertices F) = Fintype.card W - F.card by
      simp only [FreeVertices, Fintype.card_subtype_compl, Fintype.card_coe]]
    dsimp only [T]
    rw [card_sdiff_of_subset (subset_univ _), card_univ]
    have hu : (usedVertices φ ∪ U).card ≤ F.card + U.card := by
      simpa only [card_usedVertices] using card_union_le (usedVertices φ) U
    have hf := card_le_univ F
    omega
  obtain ⟨g, hg⟩ := Function.Embedding.exists_of_card_le_finset hc
  have hmem (x : FreeVertices F) : g x ∈ T := hg ⟨x, rfl⟩
  let ψ : FreeVertices F ↪ UnusedVertices φ :=
    ⟨fun x => ⟨g x, fun h => (mem_sdiff.mp (hmem x)).2 (mem_union_left _ h)⟩,
      fun x y h => g.injective (congrArg Subtype.val h)⟩
  refine ⟨completeExtension φ ψ, ?_⟩
  intro x hx
  change (if hx' : x ∈ F then φ ⟨x, hx'⟩ else (ψ ⟨x, hx'⟩).val) ∉ U
  rw [dif_neg hx]
  exact fun h => (mem_sdiff.mp (hmem ⟨x, hx⟩)).2 (mem_union_right _ h)

theorem legalExtensions_nonempty_rankOne (φ : F ↪ V) (H : Hypergraph W 1)
    (B : Hypergraph V 1) (hn : Fintype.card W + B.card ≤ Fintype.card V) :
    (legalExtensions φ H B).Nonempty := by
  obtain ⟨f, hf⟩ := exists_vertex_avoiding_extension φ (vertexSupport B)
    (by simpa only [card_vertexSupport_rankOne] using hn)
  refine ⟨f, (mem_legalExtensions φ H B f).mpr ?_⟩
  intro e _ heF heB
  obtain ⟨x, hx⟩ := card_pos.mp (by rw [e.property]; decide : 0 < e.val.card)
  have heq := one_block_eq_singleton hx
  have hxF : x ∉ F := by
    intro hxF
    exact heF (by rw [heq]; exact singleton_subset_iff.mpr hxF)
  exact hf x hxF (subset_vertexSupport heB (mem_map.mpr ⟨x, hx, rfl⟩))

end Arxiv2411_18291
