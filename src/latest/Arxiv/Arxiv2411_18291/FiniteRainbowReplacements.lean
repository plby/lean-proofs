import Arxiv.Arxiv2411_18291.FiniteNearFrameCandidates
import Arxiv.Arxiv2411_18291.FiniteColouredExtensions
import Arxiv.Arxiv2411_18291.RainbowModularGeneration

/-! # Far-clique colours and rainbow exchange replacements at n0 -/

open Finset MeasureTheory

noncomputable section

namespace Arxiv2411_18291

variable {J W : Type*} [Fintype J] [Fintype W] [DecidableEq W] {q r n h : ℕ}
variable {S : ExchangeSystem W q (r + 1)} {A : Finset (Block W q)}

theorem rainbow_exchange_replacements_failure_square_paper_threshold
    [MeasurableSpace (Equiv.Perm (Fin n))]
    [MeasurableSingletonClass (Equiv.Perm (Fin n))] (hA : IsExchangeFamily S A)
    (hqr : r + 1 < q) (hn : paperSizeThreshold q (r + 1) ≤ n)
    (hw : Fintype.card W ≤ (4 * q) ^ (2 * q)) (hqh : q.choose (r + 1) ≤ h)
    (hSh : S.graph.card ≤ h)
    (hH : h ≤ 3 * (2 * q) ^ (r + 1) * (q.choose (r + 1)) ^ 2)
    (K : Hypergraph (Fin n) (r + 1))
    (hT : IsTypical K ((n : ℝ) ^ (-(1 / 10 : ℝ))) h)
    (hd : |density K - (n : ℝ) ^ (-paperAlpha q (r + 1))| ≤
      (n : ℝ) ^ (-(1 / 10 : ℝ)) * (n : ℝ) ^ (-paperAlpha q (r + 1)))
    (D : Finset (Block (Fin n) q)) (hDK : D ⊆ cliqueFamily K q)
    (hloss : (((cliqueFamily K q) \ D).card : ℝ) ≤
      (n : ℝ) ^ (-(paperAlpha q (r + 1) / 10)) * (cliqueFamily K q).card)
    (G : Hypergraph (Fin n) (r + 1))
    (hcount : ∀ e ∈ G, |((D.filter fun Q => e.val ⊆ Q.val).card : ℝ) -
      cliqueMainTerm n (density K) q (r + 1) (r + 1)| ≤
        (n : ℝ) ^ (-(paperAlpha q (r + 1) / 10)) *
          cliqueMainTerm n (density K) q (r + 1) (r + 1))
    (σ : J → Equiv.Perm (Fin n)) :
    (IndependentTrials.probability (RandomPermutation.probability S.farCliques (Fin n))
      (paperColourTrialCount q (r + 1) S.base.val.card)).real
        {ω | ¬ ∀ Q : Block (Fin n) q,
          IsRainbow (fun j => mapGraph (σ j).toEmbedding G) (cliqueEdges (r + 1) Q) →
          ∃ f : W ↪ Fin n, mapBlock f S.base = Q ∧
            ∀ P ∈ S.replacementCliques, mapBlock f P ∈ permutedUnion σ D ∪
              permutedUnion (fun p :
                Fin (paperColourTrialCount q (r + 1) S.base.val.card) × S.farCliques =>
                  ω p.1 p.2) D} ≤ (n : ℝ) ^ (-2 : ℝ) := by
  classical
  have hh : 1 ≤ h := (Nat.succ_le_iff.mpr (Nat.choose_pos hqr.le)).trans hqh
  have hK2 : 2 ≤ q.choose (r + 1) := (show 2 ≤ q by omega).trans (q_le_choose_succ hqr)
  have hfar : S.farCliques.card ≤ h := by
    have hmul := Nat.mul_le_mul_right S.farCliques.card hK2
    have hbound := S.far_card_mul_le
    omega
  let a := paperAlpha q (r + 1) * ((q.choose (r + 1) - 1 : ℕ) : ℝ) *
    q.choose (r + 1) + 1 / 40
  let β := paperAlpha q (r + 1) * q.choose (r + 1)
  have hgap : a + 2 * β * S.farCliques.card + paperAlpha q (r + 1) / 24 ≤ 39 / 40 := by
    have hb := hA.colour_exponent_le (Nat.succ_pos r) (paperAlpha_pos hqr).le
    have hs := mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hSh) (paperAlpha_pos hqr).le
    have hc := paperAlpha_mul_configuration_le hqr hH
    have ha := (paperAlpha_le_rho hqr).trans (paperRho_le_one_div_36 hqr)
    dsimp only [a, β]
    nlinarith only [hb, hs, hc, ha]
  choose T hsize hnearT using rainbow_near_candidates_paper_threshold (J := J)
    hA hqr hn hw hSh hH K G D hd hcount σ
  have hsize' (φ : S.base.val ↪ Fin n) : ((3 / 4 : ℝ) * (n : ℝ) ^ (-a)) *
      (n : ℝ) ^ (Fintype.card W - S.base.val.card) ≤ (T φ).card := by
    simpa only [a, S.base.property] using hsize φ
  obtain ⟨hpbase, hpd, hpair⟩ := clique_colour_estimates_paper_threshold hqr hn hqh K hT hd
    D hDK hloss
  have hprob (φ : S.base.val ↪ Fin n) :=
    coloured_extension_lower_tail_of_estimates_paper_threshold hqr hn hh hH S.base.val hw
      univ (fun P : S.farCliques => P.val)
      (by simpa only [card_univ, Fintype.card_coe] using hfar)
      (fun P _ => S.far_inter_card_lt P.property) D (pow_nonneg (density_nonneg K) _)
      (by simpa only [card_univ, Fintype.card_coe] using hgap)
      hpbase hpd hpair φ (T φ) (hsize' φ)
  have hb := uniform_coloured_extensions_failure_square_paper_threshold hqr hn
    S.base.val (by rw [S.base.property]; omega) univ
      (fun P : S.farCliques => P.val) D T hprob
  refine (measureReal_mono ?_ (by finiteness)).trans hb
  intro ω hbad hω
  apply hbad
  let τ (p : Fin (paperColourTrialCount q (r + 1) S.base.val.card) × S.farCliques) := ω p.1 p.2
  intro Q hQ
  let φ := edgeRootMap S.base Q
  have hQ' : IsRainbow (fun j => mapGraph (σ j).toEmbedding G)
      (cliqueEdges (r + 1) (rootImage φ S.base Subset.rfl)) := by
    simpa only [φ, rootImage_edgeRootMap] using hQ
  obtain ⟨j, hj⟩ := hω φ
  have hp0 := density_nonneg D
  have hpos : 0 < extensionColourCount φ univ (fun P : S.farCliques => P.val) (T φ) D
      (ω j) := (by positivity : (0 : ℝ) ≤
        ((T φ).card : ℝ) * density D ^ (univ : Finset S.farCliques).card / 2).trans_lt hj
  obtain ⟨f, hfT, hfcol⟩ :=
    (extensionColourCount_pos_iff univ (fun P : S.farCliques => P.val) (T φ) D (ω j)).mp hpos
  refine ⟨f.val, (f.map_rootBlock φ S.base Subset.rfl).trans
    (rootImage_edgeRootMap S.base Q), fun P hP => ?_⟩
  by_cases hPN : P ∈ S.nearCliques
  · exact mem_union_left _ (hnearT φ hQ' f hfT P hPN)
  · have hPF : P ∈ S.farCliques := mem_sdiff.mpr ⟨hP, hPN⟩
    exact mem_union_right _ (mapGraph_subset_permutedUnion τ D (j, ⟨P, hPF⟩)
      (hfcol ⟨P, hPF⟩ (mem_univ _)))

theorem rainbow_exchange_replacements_paper_threshold (hA : IsExchangeFamily S A)
    (hqr : r + 1 < q) (hn : paperSizeThreshold q (r + 1) ≤ n)
    (hw : Fintype.card W ≤ (4 * q) ^ (2 * q)) (hqh : q.choose (r + 1) ≤ h)
    (hSh : S.graph.card ≤ h)
    (hH : h ≤ 3 * (2 * q) ^ (r + 1) * (q.choose (r + 1)) ^ 2)
    (K : Hypergraph (Fin n) (r + 1))
    (hT : IsTypical K ((n : ℝ) ^ (-(1 / 10 : ℝ))) h)
    (hd : |density K - (n : ℝ) ^ (-paperAlpha q (r + 1))| ≤
      (n : ℝ) ^ (-(1 / 10 : ℝ)) * (n : ℝ) ^ (-paperAlpha q (r + 1)))
    (D : Finset (Block (Fin n) q)) (hDK : D ⊆ cliqueFamily K q)
    (hloss : (((cliqueFamily K q) \ D).card : ℝ) ≤
      (n : ℝ) ^ (-(paperAlpha q (r + 1) / 10)) * (cliqueFamily K q).card)
    (G : Hypergraph (Fin n) (r + 1))
    (hcount : ∀ e ∈ G, |((D.filter fun Q => e.val ⊆ Q.val).card : ℝ) -
      cliqueMainTerm n (density K) q (r + 1) (r + 1)| ≤
        (n : ℝ) ^ (-(paperAlpha q (r + 1) / 10)) *
          cliqueMainTerm n (density K) q (r + 1) (r + 1))
    (σ : J → Equiv.Perm (Fin n)) :
    ∃ τ : Fin (paperColourTrialCount q (r + 1) S.base.val.card) × S.farCliques →
        Equiv.Perm (Fin n), ∀ Q : Block (Fin n) q,
      IsRainbow (fun j => mapGraph (σ j).toEmbedding G) (cliqueEdges (r + 1) Q) →
      ∃ f : W ↪ Fin n, mapBlock f S.base = Q ∧
        ∀ P ∈ S.replacementCliques,
          mapBlock f P ∈ permutedUnion σ D ∪ permutedUnion τ D := by
  classical
  let : MeasurableSpace (Equiv.Perm (Fin n)) := ⊤
  have hb := rainbow_exchange_replacements_failure_square_paper_threshold hA hqr hn
    hw hqh hSh hH K hT hd D hDK hloss G hcount σ
  have hn1 : (1 : ℝ) < n := by
    exact_mod_cast (paperSizeThreshold_one_lt hqr).trans_le hn
  have hsmall : (n : ℝ) ^ (-2 : ℝ) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg hn1 (by norm_num)
  obtain ⟨ω, hω⟩ := IndependentTrials.exists_of_failure_lt_one _ (hb.trans_lt hsmall)
  exact ⟨fun p => ω p.1 p.2, hω⟩

theorem sparse_host_rainbow_generation_failure_square_paper_threshold {N : ℕ}
    [MeasurableSpace (Equiv.Perm (Fin n))]
    [MeasurableSingletonClass (Equiv.Perm (Fin n))] (hA : IsExchangeFamily S A)
    (hqr : r + 1 < q) (hn : paperSizeThreshold q (r + 1) ≤ n)
    (hw : Fintype.card W ≤ (4 * q) ^ (2 * q)) (hqh : q.choose (r + 1) ≤ h)
    (hSh : S.graph.card ≤ h)
    (hH : h ≤ 3 * (2 * q) ^ (r + 1) * (q.choose (r + 1)) ^ 2)
    (K : Hypergraph (Fin n) (r + 1))
    (hT : IsTypical K ((n : ℝ) ^ (-(1 / 10 : ℝ))) h)
    (hd : |density K - (n : ℝ) ^ (-paperAlpha q (r + 1))| ≤
      (n : ℝ) ^ (-(1 / 10 : ℝ)) * (n : ℝ) ^ (-paperAlpha q (r + 1)))
    (C : ModularGeneratingData K (cliqueFamily K q) N)
    (hsat : (C.saturated.card : ℝ) ≤
      (n : ℝ) ^ (-(paperAlpha q (r + 1) / 10)) * (cliqueFamily K q).card)
    (hcount : ∀ e ∈ C.good,
      |((((cliqueFamily K q) \ C.saturated).filter fun Q => e.val ⊆ Q.val).card : ℝ) -
        cliqueMainTerm n (density K) q (r + 1) (r + 1)| ≤
          (n : ℝ) ^ (-(paperAlpha q (r + 1) / 10)) *
            cliqueMainTerm n (density K) q (r + 1) (r + 1))
    (σ : J → Equiv.Perm (Fin n)) :
    (IndependentTrials.probability (RandomPermutation.probability S.farCliques (Fin n))
      (paperColourTrialCount q (r + 1) S.base.val.card)).real
        {ω | ¬ ∀ Q : Block (Fin n) q,
          IsRainbow (fun j => mapGraph (σ j).toEmbedding C.good) (cliqueEdges (r + 1) Q) →
          modularCliqueVector N (r + 1) Q ∈
            generatedSubgroup (modularCliqueVector N (r + 1))
              (permutedUnion σ C.generators ∪ permutedUnion
                (fun p : Fin (paperColourTrialCount q (r + 1) S.base.val.card) ×
                  S.farCliques => ω p.1 p.2) C.generators)} ≤ (n : ℝ) ^ (-2 : ℝ) := by
  have hdel : (cliqueFamily K q) \ ((cliqueFamily K q) \ C.saturated) ⊆ C.saturated := by
    intro Q hQ
    by_contra hQS
    exact (mem_sdiff.mp hQ).2 (mem_sdiff.mpr ⟨(mem_sdiff.mp hQ).1, hQS⟩)
  have hloss : (((cliqueFamily K q) \ ((cliqueFamily K q) \ C.saturated)).card : ℝ) ≤
      (n : ℝ) ^ (-(paperAlpha q (r + 1) / 10)) * (cliqueFamily K q).card :=
    (Nat.cast_le.mpr (card_le_card hdel)).trans hsat
  have hb := rainbow_exchange_replacements_failure_square_paper_threshold hA hqr hn
    hw hqh hSh hH K hT hd ((cliqueFamily K q) \ C.saturated) sdiff_subset hloss C.good hcount σ
  refine (measureReal_mono ?_ (by finiteness)).trans hb
  intro ω hbad hω
  apply hbad
  intro Q hQ
  obtain ⟨f, hf, hrep⟩ := hω Q hQ
  rw [← hf]
  exact C.generated_of_exchange_replacements σ
    (fun p : Fin (paperColourTrialCount q (r + 1) S.base.val.card) × S.farCliques =>
      ω p.1 p.2) f hrep

theorem sparse_host_rainbow_generation_paper_threshold {N : ℕ} (hA : IsExchangeFamily S A)
    (hqr : r + 1 < q) (hn : paperSizeThreshold q (r + 1) ≤ n)
    (hw : Fintype.card W ≤ (4 * q) ^ (2 * q)) (hqh : q.choose (r + 1) ≤ h)
    (hSh : S.graph.card ≤ h)
    (hH : h ≤ 3 * (2 * q) ^ (r + 1) * (q.choose (r + 1)) ^ 2)
    (K : Hypergraph (Fin n) (r + 1))
    (hT : IsTypical K ((n : ℝ) ^ (-(1 / 10 : ℝ))) h)
    (hd : |density K - (n : ℝ) ^ (-paperAlpha q (r + 1))| ≤
      (n : ℝ) ^ (-(1 / 10 : ℝ)) * (n : ℝ) ^ (-paperAlpha q (r + 1)))
    (C : ModularGeneratingData K (cliqueFamily K q) N)
    (hsat : (C.saturated.card : ℝ) ≤
      (n : ℝ) ^ (-(paperAlpha q (r + 1) / 10)) * (cliqueFamily K q).card)
    (hcount : ∀ e ∈ C.good,
      |((((cliqueFamily K q) \ C.saturated).filter fun Q => e.val ⊆ Q.val).card : ℝ) -
        cliqueMainTerm n (density K) q (r + 1) (r + 1)| ≤
          (n : ℝ) ^ (-(paperAlpha q (r + 1) / 10)) *
            cliqueMainTerm n (density K) q (r + 1) (r + 1))
    (σ : J → Equiv.Perm (Fin n)) :
    ∃ τ : Fin (paperColourTrialCount q (r + 1) S.base.val.card) × S.farCliques →
        Equiv.Perm (Fin n), ∀ Q : Block (Fin n) q,
      IsRainbow (fun j => mapGraph (σ j).toEmbedding C.good) (cliqueEdges (r + 1) Q) →
      modularCliqueVector N (r + 1) Q ∈
        generatedSubgroup (modularCliqueVector N (r + 1))
          (permutedUnion σ C.generators ∪ permutedUnion τ C.generators) := by
  classical
  let : MeasurableSpace (Equiv.Perm (Fin n)) := ⊤
  have hb := sparse_host_rainbow_generation_failure_square_paper_threshold hA hqr hn
    hw hqh hSh hH K hT hd C hsat hcount σ
  have hn1 : (1 : ℝ) < n := by
    exact_mod_cast (paperSizeThreshold_one_lt hqr).trans_le hn
  have hsmall : (n : ℝ) ^ (-2 : ℝ) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg hn1 (by norm_num)
  obtain ⟨ω, hω⟩ := IndependentTrials.exists_of_failure_lt_one _ (hb.trans_lt hsmall)
  exact ⟨fun p => ω p.1 p.2, hω⟩

end Arxiv2411_18291
