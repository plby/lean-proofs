import Arxiv.Arxiv2411_18291.FiniteRainbowProbability
import Arxiv.Arxiv2411_18291.FiniteRainbowRootPatterns

/-! # Failure bounds for the three rainbow root patterns in one palette -/

open Finset MeasureTheory

noncomputable section

namespace Arxiv2411_18291

variable {I W : Type*} [Fintype I] [Fintype W] [DecidableEq W] {q r n h : ℕ}
variable [MeasurableSpace (Equiv.Perm (Fin n))]
variable [MeasurableSingletonClass (Equiv.Perm (Fin n))]

omit [DecidableEq W] in
theorem rainbow_punctured_cliques_failure_paper_threshold (hqr : r + 1 < q) (hq : 3 ≤ q)
    (hn : paperSizeThreshold q (r + 1) ≤ n) (hqh : q.choose (r + 1) ≤ h)
    (hH : h ≤ 3 * (2 * q) ^ (r + 1) * (q.choose (r + 1)) ^ 2)
    (F₀ : Block W (r + 1)) (hW : Fintype.card W = q)
    (K G : Hypergraph (Fin n) (r + 1))
    (hT : IsTypical K ((n : ℝ) ^ (-(1 / 10 : ℝ))) h)
    (hd : |density K - (n : ℝ) ^ (-paperAlpha q (r + 1))| ≤
      (n : ℝ) ^ (-(1 / 10 : ℝ)) * (n : ℝ) ^ (-paperAlpha q (r + 1)))
    (hGK : G ⊆ K)
    (hloss : ((K \ G).card : ℝ) ≤
      (n : ℝ) ^ (-(paperAlpha q (r + 1) / 10)) * K.card)
    (hroom : paperCommonColourTrialCount q (r + 1) * (q.choose (r + 1) - 1) ≤
      Fintype.card I) :
    (RandomPermutation.probability I (Fin n)).real
      {σ | ¬ ∀ e : Block (Fin n) (r + 1),
        ((3 / 8 : ℝ) * density G ^ (q.choose (r + 1) - 1) *
          (n : ℝ) ^ (q - (r + 1))) / (q - (r + 1)).factorial <
            (rainbowPuncturedCliques (fun i => mapGraph (σ i).toEmbedding G) e q).card} ≤
      (n : ℝ) ^ (-(5 / 3 : ℝ)) := by
  classical
  have hw : Fintype.card W ≤ (4 * q) ^ (2 * q) := by
    rw [hW]
    exact (show q ≤ 4 * q by omega).trans (Nat.le_self_pow (by omega : 2 * q ≠ 0) _)
  have hE := card_newEdges_complete_root F₀ hW
  have hEh : (newEdges F₀.val (complete W (r + 1))).card ≤ h := by
    rw [hE]
    exact (Nat.sub_le _ _).trans hqh
  have hb := rainbow_extensions_failure_paper_threshold hqr hq hn hqh hH hw F₀.val
    (by rw [F₀.property]; omega) (newEdges F₀.val (complete W (r + 1))) hEh
    (fun e he => ((mem_newEdges _ _).mp he).2) K G hT hd hGK hloss
    (by simpa only [hE] using hroom)
  refine (measureReal_mono ?_ (measure_ne_top _ _)).trans hb
  intro σ hbad hσ
  apply hbad
  intro e
  apply rainbow_cliques_card_lower F₀ hW σ G e
  simpa only [hE, hW, F₀.property] using hσ (edgeRootMap F₀ e)

omit [DecidableEq W] in
theorem rainbow_clique_roots_failure_paper_threshold (hqr : r + 1 < q) (hq : 3 ≤ q)
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
      (n : ℝ) ^ (-(paperAlpha q (r + 1) / 10)) * K.card)
    (hroom : paperCommonColourTrialCount q (r + 1) * H.card ≤ Fintype.card I) :
    (RandomPermutation.probability I (Fin n)).real
      {σ | ¬ ∀ P : Block (Fin n) q, ∃ f : W ↪ Fin n, mapBlock f P₀ = P ∧
        IsRainbow (fun i => mapGraph (σ i).toEmbedding G)
          (mapGraph f H \ cliqueEdges (r + 1) P)} ≤ (n : ℝ) ^ (-(5 / 3 : ℝ)) := by
  classical
  have hE : (newEdges P₀.val H).card ≤ h := (card_filter_le _ _).trans hHh
  have hb := rainbow_extensions_failure_paper_threshold hqr hq hn hqh hH hw P₀.val
    (by rw [P₀.property]; omega) (newEdges P₀.val H) hE
    (fun e he => ((mem_newEdges _ _).mp he).2) K G hT hd hGK hloss
    ((Nat.mul_le_mul_left _ (card_filter_le _ _)).trans hroom)
  refine (measureReal_mono ?_ (measure_ne_top _ _)).trans hb
  intro σ hbad hσ
  apply hbad
  apply rainbow_clique_root_of_extensions H P₀ σ G
  intro φ
  have hG0 := density_nonneg G
  have hpos : (0 : ℝ) < (rainbowExtensions φ (newEdges P₀.val H) σ G).card :=
    (by positivity : (0 : ℝ) ≤ (3 / 8) * density G ^ (newEdges P₀.val H).card *
      (n : ℝ) ^ (Fintype.card W - P₀.val.card)).trans_lt (hσ φ)
  exact card_pos.mp (by exact_mod_cast hpos)

theorem rainbow_pair_roots_failure_paper_threshold (hqr : r + 1 < q) (hq : 3 ≤ q)
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
      (n : ℝ) ^ (-(paperAlpha q (r + 1) / 10)) * K.card)
    (hroom : paperCommonColourTrialCount q (r + 1) * S.graph.card ≤ Fintype.card I) :
    (RandomPermutation.probability I (Fin n)).real
      {σ | ¬ ∀ P Q : Block (Fin n) q, ∀ d : Block (Fin n) (r + 1), P.val ∩ Q.val = d.val →
        ∃ f : W ↪ Fin n, mapBlock f S.base = P ∧ mapBlock f N = Q ∧
          IsRainbow (fun i => mapGraph (σ i).toEmbedding G)
            (mapGraph f S.graph \ (cliqueEdges (r + 1) P ∪ cliqueEdges (r + 1) Q))} ≤
      (n : ℝ) ^ (-(5 / 3 : ℝ)) := by
  have hE : (newEdges (S.base.val ∪ N.val) S.graph).card ≤ h := (card_filter_le _ _).trans hSh
  have hFcard := card_union_add_card_inter S.base.val N.val
  rw [hpair.vertex_inter, e₀.property, S.base.property, N.property] at hFcard
  have hb := rainbow_extensions_failure_paper_threshold hqr hq hn hqh hH hw
    (S.base.val ∪ N.val) (by omega) (newEdges (S.base.val ∪ N.val) S.graph) hE
    (fun e he => ((mem_newEdges _ _).mp he).2) K G hT hd hGK hloss
    ((Nat.mul_le_mul_left _ (card_filter_le _ _)).trans hroom)
  refine (measureReal_mono ?_ (measure_ne_top _ _)).trans hb
  intro σ hbad hσ
  apply hbad
  apply rainbow_pair_roots_of_extensions hpair σ G
  intro φ
  have hG0 := density_nonneg G
  have hpos : (0 : ℝ) <
      (rainbowExtensions φ (newEdges (S.base.val ∪ N.val) S.graph) σ G).card :=
    (by positivity : (0 : ℝ) ≤ (3 / 8) * density G ^
      (newEdges (S.base.val ∪ N.val) S.graph).card *
        (n : ℝ) ^ (Fintype.card W - (S.base.val ∪ N.val).card)).trans_lt (hσ φ)
  exact card_pos.mp (by exact_mod_cast hpos)

end Arxiv2411_18291
