import Arxiv.Arxiv2411_18291.RainbowExtensions
import Arxiv.Arxiv2411_18291.RootedCliquePattern

/-!
# Counting distinct rainbow punctured cliques

The extension count counts labelled embeddings. A fixed image clique has
at most `(q-r)!` embeddings extending the root map. Dividing by this
factorial gives a bound for distinct cliques.
-/

open Finset

noncomputable section

namespace Arxiv2411_18291

variable {I W V : Type*} [Fintype W] [Fintype V] [DecidableEq V] {q r : ℕ}
variable {F : Finset W}

theorem embeddingClique_fiber_card_le (φ : F ↪ V) (hW : Fintype.card W = q)
    (Q : Block V q) :
    (univ.filter fun f : EmbeddingExtension φ => embeddingClique hW f.val = Q).card ≤
      (q - F.card).factorial := by
  classical
  let U : Block W q := ⟨univ, by rw [card_univ, hW]⟩
  have hU : (U.val \ F).card = q - F.card := by
    rw [card_sdiff_of_subset (subset_univ F), card_univ, hW]
  have hb := edgeTargetExtensions_card_le φ U Q
  rw [hU, hW, Nat.sub_self, pow_zero, mul_one] at hb
  exact hb

omit [Fintype V] in
theorem embeddingClique_image_card_bound [Finite V] (φ : F ↪ V) (hW : Fintype.card W = q)
    (T : Finset (EmbeddingExtension φ)) :
    T.card ≤ (T.image (fun f => embeddingClique hW f.val)).card * (q - F.card).factorial := by
  classical
  let _ := Fintype.ofFinite V
  rw [card_eq_sum_card_image (fun f : EmbeddingExtension φ => embeddingClique hW f.val) T]
  calc
    _ ≤ ∑ _Q ∈ T.image (fun f => embeddingClique hW f.val), (q - F.card).factorial := by
      apply sum_le_sum
      intro Q _
      have hsub : (T.filter fun f => embeddingClique hW f.val = Q) ⊆
          (univ.filter fun f : EmbeddingExtension φ => embeddingClique hW f.val = Q) := by
        intro f hf
        exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hf).2⟩
      exact (card_le_card hsub).trans (embeddingClique_fiber_card_le φ hW Q)
    _ = _ := by simp only [sum_const, smul_eq_mul]

open Classical in
def rainbowPuncturedCliques (colour : I → Hypergraph V (r + 1)) (e : Block V (r + 1))
    (q : ℕ) : Finset (Block V q) :=
  univ.filter fun Q => e.val ⊆ Q.val ∧ IsRainbow colour ((cliqueEdges (r + 1) Q).erase e)

variable [DecidableEq W]

theorem rainbow_clique_image_subset (F₀ : Block W (r + 1)) (hW : Fintype.card W = q)
    (σ : I → Equiv.Perm V) (G : Hypergraph V (r + 1)) (e : Block V (r + 1)) :
    (rainbowExtensions (edgeRootMap F₀ e) (newEdges F₀.val (complete W (r + 1))) σ G).image
      (fun f => embeddingClique hW f.val) ⊆
        rainbowPuncturedCliques (fun i => mapGraph (σ i).toEmbedding G) e q := by
  classical
  intro Q hQ
  obtain ⟨f, hf, rfl⟩ := mem_image.mp hQ
  have hroot := edgeRootMap_usedVertices F₀ e
  have hsub : e.val ⊆ (embeddingClique hW f.val).val := by
    rw [← hroot, ← EmbeddingExtension.map_roots (edgeRootMap F₀ e) f]
    exact map_subset_map.mpr (subset_univ _)
  have hcol := (mem_rainbowExtensions _ _ _ _ f).mp hf
  rw [map_newEdges_complete_eq_erase F₀ hW (edgeRootMap F₀ e) e hroot f] at hcol
  exact mem_filter.mpr ⟨mem_univ _, hsub, hcol⟩

theorem rainbow_extensions_le_cliques_factorial (F₀ : Block W (r + 1))
    (hW : Fintype.card W = q) (σ : I → Equiv.Perm V) (G : Hypergraph V (r + 1))
    (e : Block V (r + 1)) :
    (rainbowExtensions (edgeRootMap F₀ e) (newEdges F₀.val (complete W (r + 1))) σ G).card ≤
      (rainbowPuncturedCliques (fun i => mapGraph (σ i).toEmbedding G) e q).card *
        (q - (r + 1)).factorial := by
  have hb := embeddingClique_image_card_bound (edgeRootMap F₀ e) hW
    (rainbowExtensions (edgeRootMap F₀ e) (newEdges F₀.val (complete W (r + 1))) σ G)
  rw [F₀.property] at hb
  exact hb.trans (Nat.mul_le_mul_right _ (card_le_card (rainbow_clique_image_subset F₀ hW σ G e)))

theorem rainbow_cliques_card_lower (F₀ : Block W (r + 1)) (hW : Fintype.card W = q)
    (σ : I → Equiv.Perm V) (G : Hypergraph V (r + 1)) (e : Block V (r + 1)) {A : ℝ}
    (hA : A <
      (rainbowExtensions (edgeRootMap F₀ e) (newEdges F₀.val (complete W (r + 1))) σ G).card) :
    A / (q - (r + 1)).factorial <
      (rainbowPuncturedCliques (fun i => mapGraph (σ i).toEmbedding G) e q).card := by
  apply (div_lt_iff₀ (by exact_mod_cast Nat.factorial_pos (q - (r + 1)))).mpr
  have hb :
      ((rainbowExtensions (edgeRootMap F₀ e) (newEdges F₀.val (complete W (r + 1))) σ G).card : ℝ) ≤
        (rainbowPuncturedCliques (fun i => mapGraph (σ i).toEmbedding G) e q).card *
          ((q - (r + 1)).factorial : ℝ) := by
    exact_mod_cast rainbow_extensions_le_cliques_factorial F₀ hW σ G e
  exact hA.trans_le hb

end Arxiv2411_18291
