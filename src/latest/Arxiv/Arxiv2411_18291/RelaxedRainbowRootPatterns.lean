import Arxiv.Arxiv2411_18291.RelaxedRainbowExtensions
import Arxiv.Arxiv2411_18291.RainbowCliqueExistence
import Arxiv.Arxiv2411_18291.RainbowExchangePlacements

/-! # Logarithmic palettes for punctured cliques and prescribed exchange roots -/

open Finset

noncomputable section

namespace Arxiv2411_18291

variable {W : Type*} [Fintype W] [DecidableEq W] {q r n h : ℕ}

theorem exists_rainbow_punctured_cliques_relaxed_paper_threshold (hqr : r + 1 < q)
    (hn : paperSizeThreshold q (r + 1) ≤ n) (hqh : q.choose (r + 1) ≤ h)
    (hH : h ≤ 3 * (2 * q) ^ (r + 1) * (q.choose (r + 1)) ^ 2)
    (F₀ : Block W (r + 1)) (hW : Fintype.card W = q)
    (K G : Hypergraph (Fin n) (r + 1))
    (hT : IsTypical K ((n : ℝ) ^ (-(1 / 10 : ℝ))) h)
    (hd : |density K - (n : ℝ) ^ (-paperAlpha q (r + 1))| ≤
      (n : ℝ) ^ (-(1 / 10 : ℝ)) * (n : ℝ) ^ (-paperAlpha q (r + 1)))
    (hGK : G ⊆ K)
    (hloss : ((K \ G).card : ℝ) ≤
      (n : ℝ) ^ (-(paperAlpha q (r + 1) / 60)) * K.card) :
    ∃ σ : Option (Fin (logarithmicColourTrialCount n F₀.val.card) ×
        ↥(newEdges F₀.val (complete W (r + 1)))) → Equiv.Perm (Fin n),
      ∀ e : Block (Fin n) (r + 1),
        ((3 / 8 : ℝ) * density G ^ (q.choose (r + 1) - 1) *
          (n : ℝ) ^ (q - (r + 1))) / (q - (r + 1)).factorial <
            (rainbowPuncturedCliques (fun i => mapGraph (σ i).toEmbedding G) e q).card := by
  have hw : Fintype.card W ≤ (4 * q) ^ (2 * q) := by
    rw [hW]
    exact (show q ≤ 4 * q by omega).trans (Nat.le_self_pow (by omega : 2 * q ≠ 0) _)
  have hE := card_newEdges_complete_root F₀ hW
  have hEh : (newEdges F₀.val (complete W (r + 1))).card ≤ h := by
    rw [hE]
    exact (Nat.sub_le _ _).trans hqh
  have hext := exists_many_rainbow_extensions_relaxed_paper_threshold hqr hn hqh hH hw F₀.val
    (newEdges F₀.val (complete W (r + 1))) hEh (fun e he => ((mem_newEdges _ _).mp he).2)
    K G hT hd hGK hloss
  obtain ⟨σ, hσ⟩ := hext
  refine ⟨σ, fun e => ?_⟩
  apply rainbow_cliques_card_lower F₀ hW σ G e
  simpa only [hE, hW, F₀.property] using hσ (edgeRootMap F₀ e)

theorem exists_rainbow_clique_roots_relaxed_paper_threshold (hqr : r + 1 < q)
    (hn : paperSizeThreshold q (r + 1) ≤ n) (hqh : q.choose (r + 1) ≤ h)
    (hH : h ≤ 3 * (2 * q) ^ (r + 1) * (q.choose (r + 1)) ^ 2)
    (hw : Fintype.card W ≤ (4 * q) ^ (2 * q))
    (H : Hypergraph W (r + 1)) (hHh : H.card ≤ h) (P₀ : Block W q)
    (K G : Hypergraph (Fin n) (r + 1))
    (hT : IsTypical K ((n : ℝ) ^ (-(1 / 10 : ℝ))) h)
    (hd : |density K - (n : ℝ) ^ (-paperAlpha q (r + 1))| ≤
      (n : ℝ) ^ (-(1 / 10 : ℝ)) * (n : ℝ) ^ (-paperAlpha q (r + 1)))
    (hGK : G ⊆ K)
    (hloss : ((K \ G).card : ℝ) ≤
      (n : ℝ) ^ (-(paperAlpha q (r + 1) / 60)) * K.card) :
    ∃ σ : Option (Fin (logarithmicColourTrialCount n P₀.val.card) × ↥(newEdges P₀.val H)) →
        Equiv.Perm (Fin n),
      ∀ P : Block (Fin n) q, ∃ f : W ↪ Fin n, mapBlock f P₀ = P ∧
        IsRainbow (fun i => mapGraph (σ i).toEmbedding G)
          (mapGraph f H \ cliqueEdges (r + 1) P) := by
  have hE : (newEdges P₀.val H).card ≤ h := (card_filter_le _ _).trans hHh
  have hext := exists_many_rainbow_extensions_relaxed_paper_threshold hqr hn hqh hH hw P₀.val
    (newEdges P₀.val H) hE (fun e he => ((mem_newEdges _ _).mp he).2) K G hT hd hGK hloss
  obtain ⟨σ, hσ⟩ := hext
  refine ⟨σ, rainbow_clique_root_of_extensions H P₀ σ G (fun φ => ?_)⟩
  have hG0 := density_nonneg G
  have hpos : (0 : ℝ) < (rainbowExtensions φ (newEdges P₀.val H) σ G).card :=
    (by positivity : (0 : ℝ) ≤ (3 / 8) * density G ^ (newEdges P₀.val H).card *
      (n : ℝ) ^ (Fintype.card W - P₀.val.card)).trans_lt (hσ φ)
  exact card_pos.mp (by exact_mod_cast hpos)

theorem exists_rainbow_pair_roots_relaxed_paper_threshold (hqr : r + 1 < q)
    (hn : paperSizeThreshold q (r + 1) ≤ n) (hqh : q.choose (r + 1) ≤ h)
    (hH : h ≤ 3 * (2 * q) ^ (r + 1) * (q.choose (r + 1)) ^ 2)
    (hw : Fintype.card W ≤ (4 * q) ^ (2 * q))
    {S : ExchangeSystem W q (r + 1)} {N : Block W q} {e₀ : Block W (r + 1)}
    (hpair : IsEliminationPair S N e₀) (hSh : S.graph.card ≤ h)
    (K G : Hypergraph (Fin n) (r + 1))
    (hT : IsTypical K ((n : ℝ) ^ (-(1 / 10 : ℝ))) h)
    (hd : |density K - (n : ℝ) ^ (-paperAlpha q (r + 1))| ≤
      (n : ℝ) ^ (-(1 / 10 : ℝ)) * (n : ℝ) ^ (-paperAlpha q (r + 1)))
    (hGK : G ⊆ K)
    (hloss : ((K \ G).card : ℝ) ≤
      (n : ℝ) ^ (-(paperAlpha q (r + 1) / 60)) * K.card) :
    ∃ σ : Option (Fin (logarithmicColourTrialCount n (S.base.val ∪ N.val).card) ×
        ↥(newEdges (S.base.val ∪ N.val) S.graph)) → Equiv.Perm (Fin n),
      ∀ P Q : Block (Fin n) q, ∀ d : Block (Fin n) (r + 1), P.val ∩ Q.val = d.val →
        ∃ f : W ↪ Fin n, mapBlock f S.base = P ∧ mapBlock f N = Q ∧
          IsRainbow (fun i => mapGraph (σ i).toEmbedding G)
            (mapGraph f S.graph \ (cliqueEdges (r + 1) P ∪ cliqueEdges (r + 1) Q)) := by
  have hE : (newEdges (S.base.val ∪ N.val) S.graph).card ≤ h := (card_filter_le _ _).trans hSh
  obtain ⟨σ, hσ⟩ := exists_many_rainbow_extensions_relaxed_paper_threshold hqr hn hqh hH hw
    (S.base.val ∪ N.val) (newEdges (S.base.val ∪ N.val) S.graph) hE
    (fun e he => ((mem_newEdges _ _).mp he).2) K G hT hd hGK hloss
  refine ⟨σ, rainbow_pair_roots_of_extensions hpair σ G (fun φ => ?_)⟩
  have hG0 := density_nonneg G
  have hpos : (0 : ℝ) <
      (rainbowExtensions φ (newEdges (S.base.val ∪ N.val) S.graph) σ G).card :=
    (by positivity : (0 : ℝ) ≤ (3 / 8) * density G ^
      (newEdges (S.base.val ∪ N.val) S.graph).card *
        (n : ℝ) ^ (Fintype.card W - (S.base.val ∪ N.val).card)).trans_lt (hσ φ)
  exact card_pos.mp (by exact_mod_cast hpos)

end Arxiv2411_18291
