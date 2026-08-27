import Arxiv.Arxiv2411_18291.FiniteRainbowExtensions
import Arxiv.Arxiv2411_18291.PermutationColourConditioning
import Arxiv.Arxiv2411_18291.FiniteColourPaletteBudget

/-! # Failure probabilities for many rainbow extensions inside a prescribed palette -/

open Finset MeasureTheory

noncomputable section

namespace Arxiv2411_18291

variable {I W : Type*} [Fintype W] {q r n h : ℕ}
variable [MeasurableSpace (Equiv.Perm (Fin n))]
variable [MeasurableSingletonClass (Equiv.Perm (Fin n))]

theorem rainbow_extensions_failure_of_trials_of_bound {L : ℕ}
    (hqr : r + 1 < q) (hn : paperSizeThreshold q (r + 1) ≤ n)
    (hqh : q.choose (r + 1) ≤ h)
    (hH : h ≤ 3 * (2 * q) ^ (r + 1) * (q.choose (r + 1)) ^ 2)
    (hw : Fintype.card W ≤ (4 * q) ^ (2 * q)) (F : Finset W)
    (E : Hypergraph W (r + 1)) (hEh : E.card ≤ h) (hroot : ∀ e ∈ E, ¬e.val ⊆ F)
    (K G : Hypergraph (Fin n) (r + 1))
    (hT : IsTypical K ((n : ℝ) ^ (-(1 / 10 : ℝ))) h)
    (hd : |density K - (n : ℝ) ^ (-paperAlpha q (r + 1))| ≤
      (n : ℝ) ^ (-(1 / 10 : ℝ)) * (n : ℝ) ^ (-paperAlpha q (r + 1)))
    (hGK : G ⊆ K)
    (hloss : ((K \ G).card : ℝ) ≤
      (n : ℝ) ^ (-(paperAlpha q (r + 1) / 10)) * K.card)
    (e : Fin L × E ↪ I)
    (hfail : (n : ℝ) ^ F.card * (8 * (n : ℝ) ^ (-(paperAlpha q (r + 1) / 24))) ^ L ≤
      (n : ℝ) ^ (-(5 / 3 : ℝ))) :
    (RandomPermutation.probability I (Fin n)).real
      {σ | ¬ ∀ φ : F ↪ Fin n,
        (3 / 8 : ℝ) * density G ^ E.card * (n : ℝ) ^ (Fintype.card W - F.card) <
          (rainbowExtensions φ E σ G).card} ≤ (n : ℝ) ^ (-(5 / 3 : ℝ)) := by
  classical
  have hnsize := paper_small_carrier_completion_size hqr hn hw
  have hroot' : ∀ e ∈ (univ : Finset E), (e.val.val ∩ F).card < r + 1 :=
    fun e _ => block_root_inter_card_lt e.val (hroot e.val e.property)
  have hsize (φ : F ↪ Fin n) : (3 / 4 : ℝ) *
      (n : ℝ) ^ (Fintype.card W - F.card) ≤ (univ : Finset (EmbeddingExtension φ)).card := by
    simpa only [card_univ, Fintype.card_fin] using card_embeddingExtension_three_quarters φ
      (by simpa only [Fintype.card_fin] using hnsize)
  have hprob (φ : F ↪ Fin n) := coloured_extension_lower_tail_paper_threshold
    hqr hn hqh hH F hw univ (fun e : E => e.val)
    (by simpa only [card_univ, Fintype.card_coe] using hEh) hroot'
    K G hT hd hGK hloss φ univ (hsize φ)
  let B : Set (Fin L →
      RandomPermutation.Sample E (Fin n)) :=
    {ω | ¬ ∀ φ : F ↪ Fin n, ∃ j,
      ((univ : Finset (EmbeddingExtension φ)).card : ℝ) *
        density G ^ (univ : Finset E).card / 2 <
          extensionColourCount φ univ (fun e : E => e.val) univ G (ω j)}
  have hB : (IndependentTrials.probability (RandomPermutation.probability E (Fin n))
      L).real B ≤ (n : ℝ) ^ (-(5 / 3 : ℝ)) :=
    (uniform_coloured_extensions_failure_bound F univ (fun e : E => e.val) G
      (fun _ => univ) (by positivity) hprob).trans
        hfail
  have hpull := (RandomPermutation.probability_trial_event e B).trans_le hB
  refine (measureReal_mono ?_ (measure_ne_top _ _)).trans hpull
  intro σ hbad hsuccess
  apply hbad
  intro φ
  obtain ⟨j, hj⟩ := hsuccess φ
  simp only [card_univ, Fintype.card_coe] at hj
  have hs := hsize φ
  rw [card_univ] at hs
  have hm := mul_le_mul_of_nonneg_right hs (pow_nonneg (density_nonneg G) E.card)
  have hmean : (3 / 8 : ℝ) * density G ^ E.card *
      (n : ℝ) ^ (Fintype.card W - F.card) ≤
        (Fintype.card (EmbeddingExtension φ) : ℝ) * density G ^ E.card / 2 := by
    nlinarith only [hm]
  exact (hmean.trans_lt hj).trans_le
    (extensionColourCount_le_rainbow_card_injected φ E G σ e j)

theorem rainbow_extensions_failure_of_trials_paper_threshold
    (hqr : r + 1 < q) (hq : 3 ≤ q) (hn : paperSizeThreshold q (r + 1) ≤ n)
    (hqh : q.choose (r + 1) ≤ h)
    (hH : h ≤ 3 * (2 * q) ^ (r + 1) * (q.choose (r + 1)) ^ 2)
    (hw : Fintype.card W ≤ (4 * q) ^ (2 * q)) (F : Finset W) (hF : F.card ≤ 2 * q - 1)
    (E : Hypergraph W (r + 1)) (hEh : E.card ≤ h) (hroot : ∀ e ∈ E, ¬e.val ⊆ F)
    (K G : Hypergraph (Fin n) (r + 1))
    (hT : IsTypical K ((n : ℝ) ^ (-(1 / 10 : ℝ))) h)
    (hd : |density K - (n : ℝ) ^ (-paperAlpha q (r + 1))| ≤
      (n : ℝ) ^ (-(1 / 10 : ℝ)) * (n : ℝ) ^ (-paperAlpha q (r + 1)))
    (hGK : G ⊆ K)
    (hloss : ((K \ G).card : ℝ) ≤
      (n : ℝ) ^ (-(paperAlpha q (r + 1) / 10)) * K.card)
    (e : Fin (paperCommonColourTrialCount q (r + 1)) × E ↪ I) :
    (RandomPermutation.probability I (Fin n)).real
      {σ | ¬ ∀ φ : F ↪ Fin n,
        (3 / 8 : ℝ) * density G ^ E.card * (n : ℝ) ^ (Fintype.card W - F.card) <
          (rainbowExtensions φ E σ G).card} ≤ (n : ℝ) ^ (-(5 / 3 : ℝ)) := by
  exact rainbow_extensions_failure_of_trials_of_bound hqr hn hqh hH hw F E hEh hroot
    K G hT hd hGK hloss e (common_colour_trial_union_bound_paper_threshold hqr hq hn hF)

theorem rainbow_extensions_failure_paper_threshold [Fintype I]
    (hqr : r + 1 < q) (hq : 3 ≤ q) (hn : paperSizeThreshold q (r + 1) ≤ n)
    (hqh : q.choose (r + 1) ≤ h)
    (hH : h ≤ 3 * (2 * q) ^ (r + 1) * (q.choose (r + 1)) ^ 2)
    (hw : Fintype.card W ≤ (4 * q) ^ (2 * q)) (F : Finset W) (hF : F.card ≤ 2 * q - 1)
    (E : Hypergraph W (r + 1)) (hEh : E.card ≤ h) (hroot : ∀ e ∈ E, ¬e.val ⊆ F)
    (K G : Hypergraph (Fin n) (r + 1))
    (hT : IsTypical K ((n : ℝ) ^ (-(1 / 10 : ℝ))) h)
    (hd : |density K - (n : ℝ) ^ (-paperAlpha q (r + 1))| ≤
      (n : ℝ) ^ (-(1 / 10 : ℝ)) * (n : ℝ) ^ (-paperAlpha q (r + 1)))
    (hGK : G ⊆ K)
    (hloss : ((K \ G).card : ℝ) ≤
      (n : ℝ) ^ (-(paperAlpha q (r + 1) / 10)) * K.card)
    (hroom : paperCommonColourTrialCount q (r + 1) * E.card ≤ Fintype.card I) :
    (RandomPermutation.probability I (Fin n)).real
      {σ | ¬ ∀ φ : F ↪ Fin n,
        (3 / 8 : ℝ) * density G ^ E.card * (n : ℝ) ^ (Fintype.card W - F.card) <
          (rainbowExtensions φ E σ G).card} ≤ (n : ℝ) ^ (-(5 / 3 : ℝ)) := by
  have hc : Fintype.card (Fin (paperCommonColourTrialCount q (r + 1)) × E) ≤
      Fintype.card I := by
    simpa only [Fintype.card_prod, Fintype.card_fin, Fintype.card_coe] using hroom
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hc
  exact rainbow_extensions_failure_of_trials_paper_threshold hqr hq hn hqh hH hw F hF
    E hEh hroot K G hT hd hGK hloss e

end Arxiv2411_18291
