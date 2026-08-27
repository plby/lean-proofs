import Arxiv.Arxiv2411_18291.FiniteExclusiveColourCounts
import Arxiv.Arxiv2411_18291.ExclusiveColourTrials
import Arxiv.Arxiv2411_18291.PermutationColourConditioning
import Arxiv.Arxiv2411_18291.RainbowColourRelabeling
import Arxiv.Arxiv2411_18291.RainbowCliqueExistence

/-! # The printed punctured-clique count without a factorial loss -/

open Finset MeasureTheory

noncomputable section

namespace Arxiv2411_18291

theorem exclusive_punctured_extensions_card_le_reindex {I W V : Type*}
    [Fintype W] [Fintype V] [DecidableEq W] [DecidableEq V] {q r : ℕ}
    (F₀ : Block W (r + 1)) (hW : Fintype.card W = q) (hqr : r + 1 < q)
    (σ : I → Equiv.Perm V) (c : (newEdges F₀.val (complete W (r + 1))) ↪ I)
    (G : Hypergraph V (r + 1)) (e : Block V (r + 1)) :
    (exclusiveColourExtensions (edgeRootMap F₀ e)
      (newEdges F₀.val (complete W (r + 1))) (fun i => σ (c i)) G).card ≤
        (rainbowPuncturedCliques (fun i => mapGraph (σ i).toEmbedding G) e q).card :=
  (exclusive_punctured_extensions_card_le F₀ hW hqr (fun i => σ (c i)) G e).trans
    (card_le_card (rainbowPuncturedCliques_subset_reindex _ σ G c (fun _ => rfl) e))

variable {I W : Type*} [Fintype W] [DecidableEq W] {q r n h : ℕ}
variable [MeasurableSpace (Equiv.Perm (Fin n))]
variable [MeasurableSingletonClass (Equiv.Perm (Fin n))]

theorem printed_punctured_colour_failure_of_trials_of_bound {L : ℕ}
    (hqr : r + 1 < q) (hn : paperSizeThreshold q (r + 1) ≤ n)
    (hqh : q.choose (r + 1) ≤ h)
    (hH : h ≤ 3 * (2 * q) ^ (r + 1) * (q.choose (r + 1)) ^ 2)
    (F₀ : Block W (r + 1)) (hW : Fintype.card W = q)
    (K G : Hypergraph (Fin n) (r + 1))
    (hT : IsTypical K ((n : ℝ) ^ (-(1 / 10 : ℝ))) h)
    (hd : |density K - (n : ℝ) ^ (-paperAlpha q (r + 1))| ≤
      (n : ℝ) ^ (-(1 / 10 : ℝ)) * (n : ℝ) ^ (-paperAlpha q (r + 1)))
    (hGK : G ⊆ K)
    (hloss : ((K \ G).card : ℝ) ≤
      (n : ℝ) ^ (-(paperAlpha q (r + 1) / 10)) * K.card)
    (e : Fin L ×
      (newEdges F₀.val (complete W (r + 1))) ↪ I)
    (hfail : (n : ℝ) ^ (r + 1) *
      (33 * (n : ℝ) ^ (-(paperAlpha q (r + 1) / 24))) ^ L ≤
        (n : ℝ) ^ (-(5 / 3 : ℝ))) :
    (RandomPermutation.probability I (Fin n)).real
      {σ | ¬ ∀ d : Block (Fin n) (r + 1),
        (1 / 2 : ℝ) * ((n : ℝ) ^ (-paperAlpha q (r + 1))) ^ (q.choose (r + 1) - 1) *
          (n : ℝ) ^ (q - (r + 1)) <
            (rainbowPuncturedCliques (fun i => mapGraph (σ i).toEmbedding G) d q).card} ≤
      (n : ℝ) ^ (-(5 / 3 : ℝ)) := by
  classical
  let E := newEdges F₀.val (complete W (r + 1))
  let b := (35 / 64 : ℝ) * density G ^ E.card * (n : ℝ) ^ (Fintype.card W - F₀.val.card)
  let B (φ : F₀.val ↪ Fin n) : Set (RandomPermutation.Sample E (Fin n)) :=
    {ω | ((exclusiveColourExtensions φ E ω G).card : ℝ) ≤ b}
  let Bad : Set (Fin L → RandomPermutation.Sample E (Fin n)) :=
    ⋃ φ ∈ (univ : Finset (F₀.val ↪ Fin n)), IndependentTrials.allBad L (B φ)
  have hE : E.card = q.choose (r + 1) - 1 := card_newEdges_complete_root F₀ hW
  have hEcard : E.card ≤ q.choose (r + 1) := hE ▸ Nat.sub_le _ _
  have hw : Fintype.card W ≤ (4 * q) ^ (2 * q) := by
    rw [hW]
    exact (show q ≤ 4 * q by omega).trans (Nat.le_self_pow (by omega : 2 * q ≠ 0) _)
  have hprob (φ : F₀.val ↪ Fin n) :
      (RandomPermutation.probability E (Fin n)).real (B φ) ≤
        33 * (n : ℝ) ^ (-(paperAlpha q (r + 1) / 24)) :=
    exclusiveColourExtensions_lower_tail_paper_threshold hqr hn hqh hH F₀.val φ E hEcard hw
      (fun e he => ((mem_newEdges _ _).mp he).2) K G hT hd hGK hloss
  have hcard : ((univ : Finset (F₀.val ↪ Fin n)).card : ℝ) ≤ (n : ℝ) ^ F₀.val.card := by
    have hh : (univ : Finset (F₀.val ↪ Fin n)).card ≤ n ^ F₀.val.card := by
      simpa only [card_univ, Fintype.card_embedding_eq, Fintype.card_fin,
        Fintype.card_coe] using Nat.descFactorial_le_pow n F₀.val.card
    exact_mod_cast hh
  have hbad : (IndependentTrials.probability (RandomPermutation.probability E (Fin n)) L).real
      Bad ≤ (n : ℝ) ^ (-(5 / 3 : ℝ)) := by
    have hb := IndependentTrials.probability_some_allBad_le
      (RandomPermutation.probability E (Fin n)) L univ B
      (fun φ _ => (Set.toFinite (B φ)).measurableSet) (fun φ _ => hprob φ)
    exact hb.trans ((mul_le_mul_of_nonneg_right hcard (by positivity)).trans
      (by simpa only [F₀.property] using hfail))
  have hpull := (RandomPermutation.probability_trial_event e Bad).trans_le hbad
  refine (measureReal_mono ?_ (measure_ne_top _ _)).trans hpull
  intro σ hfailure
  by_contra hsuccess
  apply hfailure
  intro d
  let φ := edgeRootMap F₀ d
  have htrial : ∃ j : Fin L, (fun i => σ (e (j, i))) ∉ B φ := by
    by_contra! hh
    exact hsuccess (Set.mem_iUnion.mpr ⟨φ, Set.mem_iUnion.mpr ⟨mem_univ _, hh⟩⟩)
  obtain ⟨j, hj⟩ := htrial
  have hj' : b < ((exclusiveColourExtensions φ E (fun i => σ (e (j, i))) G).card : ℝ) :=
    lt_of_not_ge hj
  let c : E ↪ I := ⟨fun i => e (j, i), fun _ _ hh => (Prod.mk.inj (e.injective hh)).2⟩
  have hcount := exclusive_punctured_extensions_card_le_reindex F₀ hW hqr σ c G d
  have hpd := good_reference_density_power_fifteen_sixteenths hqr hn
    (s := q.choose (r + 1) - 1) (Nat.sub_le _ _) K G hd hGK hloss
  have hp0 : 0 ≤ ((n : ℝ) ^ (-paperAlpha q (r + 1))) ^ (q.choose (r + 1) - 1) := by
    positivity
  have hmargin : (1 / 2 : ℝ) *
      ((n : ℝ) ^ (-paperAlpha q (r + 1))) ^ (q.choose (r + 1) - 1) ≤
        (35 / 64 : ℝ) * density G ^ (q.choose (r + 1) - 1) := by
    nlinarith only [hpd, hp0]
  have hb : (1 / 2 : ℝ) *
      ((n : ℝ) ^ (-paperAlpha q (r + 1))) ^ (q.choose (r + 1) - 1) *
        (n : ℝ) ^ (q - (r + 1)) ≤ b := by
    simpa only [b, hE, hW, F₀.property] using
      mul_le_mul_of_nonneg_right hmargin (pow_nonneg (Nat.cast_nonneg n) (q - (r + 1)))
  exact (hb.trans_lt hj').trans_le (Nat.cast_le.mpr hcount)

theorem printed_punctured_colour_failure_of_trials_paper_threshold
    (hqr : r + 1 < q) (hq : 3 ≤ q) (hn : paperSizeThreshold q (r + 1) ≤ n)
    (hqh : q.choose (r + 1) ≤ h)
    (hH : h ≤ 3 * (2 * q) ^ (r + 1) * (q.choose (r + 1)) ^ 2)
    (F₀ : Block W (r + 1)) (hW : Fintype.card W = q)
    (K G : Hypergraph (Fin n) (r + 1))
    (hT : IsTypical K ((n : ℝ) ^ (-(1 / 10 : ℝ))) h)
    (hd : |density K - (n : ℝ) ^ (-paperAlpha q (r + 1))| ≤
      (n : ℝ) ^ (-(1 / 10 : ℝ)) * (n : ℝ) ^ (-paperAlpha q (r + 1)))
    (hGK : G ⊆ K)
    (hloss : ((K \ G).card : ℝ) ≤
      (n : ℝ) ^ (-(paperAlpha q (r + 1) / 10)) * K.card)
    (e : Fin (paperCommonColourTrialCount q (r + 1)) ×
      (newEdges F₀.val (complete W (r + 1))) ↪ I) :
    (RandomPermutation.probability I (Fin n)).real
      {σ | ¬ ∀ d : Block (Fin n) (r + 1),
        (1 / 2 : ℝ) * ((n : ℝ) ^ (-paperAlpha q (r + 1))) ^ (q.choose (r + 1) - 1) *
          (n : ℝ) ^ (q - (r + 1)) <
            (rainbowPuncturedCliques (fun i => mapGraph (σ i).toEmbedding G) d q).card} ≤
      (n : ℝ) ^ (-(5 / 3 : ℝ)) := by
  exact printed_punctured_colour_failure_of_trials_of_bound hqr hn hqh hH F₀ hW
    K G hT hd hGK hloss e
    (exclusive_colour_trial_union_bound_paper_threshold hqr hq hn (by omega))

omit [DecidableEq W] in
theorem printed_rainbow_punctured_cliques_failure_paper_threshold [Fintype I]
    (hqr : r + 1 < q) (hq : 3 ≤ q) (hn : paperSizeThreshold q (r + 1) ≤ n)
    (hqh : q.choose (r + 1) ≤ h)
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
      {σ | ¬ ∀ d : Block (Fin n) (r + 1),
        (1 / 2 : ℝ) * ((n : ℝ) ^ (-paperAlpha q (r + 1))) ^ (q.choose (r + 1) - 1) *
          (n : ℝ) ^ (q - (r + 1)) <
            (rainbowPuncturedCliques (fun i => mapGraph (σ i).toEmbedding G) d q).card} ≤
      (n : ℝ) ^ (-(5 / 3 : ℝ)) := by
  classical
  have hc : Fintype.card (Fin (paperCommonColourTrialCount q (r + 1)) ×
      (newEdges F₀.val (complete W (r + 1)))) ≤ Fintype.card I := by
    simpa only [Fintype.card_prod, Fintype.card_fin, Fintype.card_coe,
      card_newEdges_complete_root F₀ hW] using hroom
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hc
  exact printed_punctured_colour_failure_of_trials_paper_threshold hqr hq hn hqh hH
    F₀ hW K G hT hd hGK hloss e

end Arxiv2411_18291
