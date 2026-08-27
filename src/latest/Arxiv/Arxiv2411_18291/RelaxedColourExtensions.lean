import Arxiv.Arxiv2411_18291.RelaxedColourNumerics
import Arxiv.Arxiv2411_18291.OneSidedSecondMoment
import Arxiv.Arxiv2411_18291.FiniteColouredExtensions
import Arxiv.Arxiv2411_18291.LogarithmicColourTrials

/-! # Actual colour trials with the relaxed good-host error

The edge-capped generators' error gives a constant second-moment ratio.
A one-sided estimate gives success probability at least one ninth in each
trial, uniformly over every prescribed root embedding.
-/

open Finset MeasureTheory

noncomputable section

namespace Arxiv2411_18291

variable {q r n h : ℕ}
variable [MeasurableSpace (Equiv.Perm (Fin n))]
variable [MeasurableSingletonClass (Equiv.Perm (Fin n))]

theorem good_edge_colour_estimates_relaxed_paper_threshold (hqr : r + 1 < q)
    (hn : paperSizeThreshold q (r + 1) ≤ n) (hqh : q.choose (r + 1) ≤ h)
    (hH : h ≤ 3 * (2 * q) ^ (r + 1) * (q.choose (r + 1)) ^ 2)
    (K G : Hypergraph (Fin n) (r + 1))
    (hT : IsTypical K ((n : ℝ) ^ (-(1 / 10 : ℝ))) h)
    (hd : |density K - (n : ℝ) ^ (-paperAlpha q (r + 1))| ≤
      (n : ℝ) ^ (-(1 / 10 : ℝ)) * (n : ℝ) ^ (-paperAlpha q (r + 1)))
    (hGK : G ⊆ K)
    (hloss : ((K \ G).card : ℝ) ≤
      (n : ℝ) ^ (-(paperAlpha q (r + 1) / 60)) * K.card) :
    (1 / 4 : ℝ) * (n : ℝ) ^ (-paperAlpha q (r + 1)) ≤ density G ∧
      (1 - (n : ℝ) ^ (-(paperAlpha q (r + 1) / 60))) * density K ≤ density G ∧
      ∀ j < r + 1, ∀ P : IntersectingBlockPair (Fin n) (r + 1) (r + 1) j,
        (PMF.uniformOfFintype (Equiv.Perm (Fin n))).toMeasure.real
          {σ | P.val.1 ∈ mapGraph σ.toEmbedding G ∧ P.val.2 ∈ mapGraph σ.toEmbedding G} ≤
          (1 + (n : ℝ) ^ (-(paperAlpha q (r + 1) / 60))) * density K ^ 2 := by
  have hh : 1 ≤ h := (Nat.choose_pos hqr.le).trans_le hqh
  have hsmall := relaxed_colour_error_le_eighth_paper_threshold hqr hn hh hH
  have hgood := density_good_lower hGK hloss
  have hK := (paper_host_density_bounds hqr hn K hd).1
  have hm := mul_le_mul_of_nonneg_right hsmall (density_nonneg K)
  refine ⟨by nlinarith only [hm, hgood, hK, density_nonneg K], hgood, ?_⟩
  intro j hj P
  have hzero : ((K \ K).card : ℝ) ≤
      (n : ℝ) ^ (-(paperAlpha q (r + 1) / 10)) * K.card := by
    rw [Finset.sdiff_self, Finset.card_empty, Nat.cast_zero]
    positivity
  have hpair := (good_edge_colour_estimates_paper_threshold hqr hn hqh K K hT hd
    (Subset.refl K) hzero).2.2 j hj P
  have hsub : {σ : Equiv.Perm (Fin n) |
      P.val.1 ∈ mapGraph σ.toEmbedding G ∧ P.val.2 ∈ mapGraph σ.toEmbedding G} ⊆
      {σ | P.val.1 ∈ mapGraph σ.toEmbedding K ∧ P.val.2 ∈ mapGraph σ.toEmbedding K} :=
    fun σ hσ => ⟨mapGraph_mono σ.toEmbedding hGK hσ.1, mapGraph_mono σ.toEmbedding hGK hσ.2⟩
  have hn1 : (1 : ℝ) ≤ n := by
    exact_mod_cast (paperSizeThreshold_one_lt hqr).le.trans hn
  have he : (n : ℝ) ^ (-(paperAlpha q (r + 1) / 12)) ≤
      (n : ℝ) ^ (-(paperAlpha q (r + 1) / 60)) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [paperAlpha_pos hqr])
  exact (measureReal_mono (μ := (PMF.uniformOfFintype (Equiv.Perm (Fin n))).toMeasure)
    hsub).trans (hpair.trans
      (mul_le_mul_of_nonneg_right (add_le_add (le_refl 1) he) (sq_nonneg _)))

theorem coloured_extension_lower_tail_relaxed_paper_threshold {I W : Type*}
    [Fintype W] [DecidableEq W] (hqr : r + 1 < q)
    (hn : paperSizeThreshold q (r + 1) ≤ n) (hqh : q.choose (r + 1) ≤ h)
    (hH : h ≤ 3 * (2 * q) ^ (r + 1) * (q.choose (r + 1)) ^ 2)
    (F : Finset W) (hw : Fintype.card W ≤ (4 * q) ^ (2 * q))
    (s : Finset I) (Q : I → Block W (r + 1)) (hs : s.card ≤ h)
    (hroot : ∀ i ∈ s, ((Q i).val ∩ F).card < r + 1)
    (K G : Hypergraph (Fin n) (r + 1))
    (hT : IsTypical K ((n : ℝ) ^ (-(1 / 10 : ℝ))) h)
    (hd : |density K - (n : ℝ) ^ (-paperAlpha q (r + 1))| ≤
      (n : ℝ) ^ (-(1 / 10 : ℝ)) * (n : ℝ) ^ (-paperAlpha q (r + 1)))
    (hGK : G ⊆ K)
    (hloss : ((K \ G).card : ℝ) ≤
      (n : ℝ) ^ (-(paperAlpha q (r + 1) / 60)) * K.card)
    (φ : F ↪ Fin n) (T : Finset (EmbeddingExtension φ))
    (hsize : (3 / 4 : ℝ) * (n : ℝ) ^ (Fintype.card W - F.card) ≤ T.card) :
    (RandomPermutation.probability I (Fin n)).real
      {ω | extensionColourCount φ s Q T G ω ≤ (T.card : ℝ) * density G ^ s.card / 2} ≤
        8 / 9 := by
  have hh : 1 ≤ h := (Nat.choose_pos hqr.le).trans_le hqh
  have hn1 : (1 : ℝ) ≤ n := by
    exact_mod_cast (paperSizeThreshold_one_lt hqr).le.trans hn
  have hn0 : (0 : ℝ) < n := zero_lt_one.trans_le hn1
  obtain ⟨hpbase, hpd, hpair⟩ := good_edge_colour_estimates_relaxed_paper_threshold
    hqr hn hqh hH K G hT hd hGK hloss
  have hp : 0 < density G := (by positivity :
    (0 : ℝ) < (1 / 4 : ℝ) * (n : ℝ) ^ (-paperAlpha q (r + 1))).trans_le hpbase
  let t := (1 + (n : ℝ) ^ (-(paperAlpha q (r + 1) / 60))) * density K ^ 2
  have ht : 0 ≤ t := by dsimp only [t]; positivity
  have hpower := relaxed_colour_joint_power_paper_threshold hqr hn hh hH
    (density_nonneg K) ht hpd (le_refl t) s.card hs
  have hc := colour_collision_bound_paper_threshold hqr hn hh hH
    ((Nat.sub_le (Fintype.card W) F.card).trans hw) hs (T.card : ℝ) (density G) hsize hpbase
  have he : (n : ℝ) ^ (-(paperAlpha q (r + 1) / 24)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hn1 (by linarith only [paperAlpha_pos hqr])
  have hcollision : ((Fintype.card W - F.card : ℕ) : ℝ) ^ 2 *
      (Fintype.card (Fin n) : ℝ) ^ (Fintype.card W - F.card - 1) ≤
        1 * T.card * density G ^ (2 * s.card) := by
    simp only [Fintype.card_fin]
    exact hc.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right he (Nat.cast_nonneg T.card)) (by positivity))
  have hsecond := extensionColourCount_relative_second_moment s Q T G (r + 1)
    ht hroot hpair (by simpa only [one_add_one_eq_two] using hpower) hcollision
  have hμ : (0 : ℝ) < T.card * density G ^ s.card :=
    mul_pos ((by positivity : (0 : ℝ) <
      (3 / 4 : ℝ) * (n : ℝ) ^ (Fintype.card W - F.card)).trans_le hsize) (pow_pos hp _)
  apply lower_tail_le_eight_ninths_of_second_moment (RandomPermutation.probability I (Fin n))
    (RandomPermutation.eventCount_memLp_two s T (fun f i => extensionColourEvent (Q i) f G))
    hμ (extensionColourCount_mean s Q T G)
  norm_num only [mul_one] at hsecond
  exact hsecond

theorem uniform_coloured_extensions_relaxed_failure_paper_threshold {I W : Type*}
    [Fintype W] [DecidableEq W] (hqr : r + 1 < q)
    (hn : paperSizeThreshold q (r + 1) ≤ n) (hqh : q.choose (r + 1) ≤ h)
    (hH : h ≤ 3 * (2 * q) ^ (r + 1) * (q.choose (r + 1)) ^ 2)
    (F : Finset W) (hw : Fintype.card W ≤ (4 * q) ^ (2 * q))
    (s : Finset I) (Q : I → Block W (r + 1)) (hs : s.card ≤ h)
    (hroot : ∀ i ∈ s, ((Q i).val ∩ F).card < r + 1)
    (K G : Hypergraph (Fin n) (r + 1))
    (hT : IsTypical K ((n : ℝ) ^ (-(1 / 10 : ℝ))) h)
    (hd : |density K - (n : ℝ) ^ (-paperAlpha q (r + 1))| ≤
      (n : ℝ) ^ (-(1 / 10 : ℝ)) * (n : ℝ) ^ (-paperAlpha q (r + 1)))
    (hGK : G ⊆ K)
    (hloss : ((K \ G).card : ℝ) ≤
      (n : ℝ) ^ (-(paperAlpha q (r + 1) / 60)) * K.card)
    (T : (φ : F ↪ Fin n) → Finset (EmbeddingExtension φ))
    (hsize : ∀ φ, (3 / 4 : ℝ) * (n : ℝ) ^ (Fintype.card W - F.card) ≤ (T φ).card) :
    (IndependentTrials.probability (RandomPermutation.probability I (Fin n))
      (logarithmicColourTrialCount n F.card)).real
        {ω | ¬ ∀ φ : F ↪ Fin n, ∃ j,
          ((T φ).card : ℝ) * density G ^ s.card / 2 <
            extensionColourCount φ s Q (T φ) G (ω j)} ≤ (n : ℝ) ^ (-2 : ℝ) := by
  have hsingle (φ : F ↪ Fin n) := coloured_extension_lower_tail_relaxed_paper_threshold
    hqr hn hqh hH F hw s Q hs hroot K G hT hd hGK hloss φ (T φ) (hsize φ)
  exact (uniform_coloured_extensions_failure_bound F s Q G T
    (by norm_num : (0 : ℝ) ≤ 8 / 9) hsingle).trans
      (logarithmic_colour_trial_union_bound
        (Nat.zero_lt_one.trans ((paperSizeThreshold_one_lt hqr).trans_le hn)) F.card)

theorem coloured_extension_lower_tail_of_estimates_relaxed_paper_threshold {I W : Type*}
    [Fintype W] [DecidableEq W] {k : ℕ}
    (hqr : r + 1 < q) (hn : paperSizeThreshold q (r + 1) ≤ n) (hh : 1 ≤ h)
    (hH : h ≤ 3 * (2 * q) ^ (r + 1) * (q.choose (r + 1)) ^ 2)
    (F : Finset W) (hw : Fintype.card W ≤ (4 * q) ^ (2 * q))
    (s : Finset I) (Q : I → Block W k) (hs : s.card ≤ h)
    (hroot : ∀ i ∈ s, ((Q i).val ∩ F).card < r + 1)
    (D : Finset (Block (Fin n) k)) {a β d : ℝ} (hd : 0 ≤ d)
    (hgap : a + 2 * β * s.card + paperAlpha q (r + 1) / 24 ≤ 39 / 40)
    (hpbase : (1 / 4 : ℝ) * (n : ℝ) ^ (-β) ≤ density D)
    (hpd : (1 - (n : ℝ) ^ (-(paperAlpha q (r + 1) / 60))) * d ≤ density D)
    (hpair : ∀ j < r + 1, ∀ P : IntersectingBlockPair (Fin n) k k j,
      (PMF.uniformOfFintype (Equiv.Perm (Fin n))).toMeasure.real
        {σ | P.val.1 ∈ mapGraph σ.toEmbedding D ∧ P.val.2 ∈ mapGraph σ.toEmbedding D} ≤
        (1 + (n : ℝ) ^ (-(paperAlpha q (r + 1) / 60))) * d ^ 2)
    (φ : F ↪ Fin n) (T : Finset (EmbeddingExtension φ))
    (hsize : ((3 / 4 : ℝ) * (n : ℝ) ^ (-a)) *
      (n : ℝ) ^ (Fintype.card W - F.card) ≤ T.card) :
    (RandomPermutation.probability I (Fin n)).real
      {ω | extensionColourCount φ s Q T D ω ≤ (T.card : ℝ) * density D ^ s.card / 2} ≤
        8 / 9 := by
  have hn1 : (1 : ℝ) ≤ n := by
    exact_mod_cast (paperSizeThreshold_one_lt hqr).le.trans hn
  have hn0 : (0 : ℝ) < n := zero_lt_one.trans_le hn1
  have hTpos : (0 : ℝ) < T.card := (by positivity : (0 : ℝ) <
    ((3 / 4 : ℝ) * (n : ℝ) ^ (-a)) * (n : ℝ) ^ (Fintype.card W - F.card)).trans_le hsize
  have hp : 0 < density D :=
    (by positivity : (0 : ℝ) < (1 / 4 : ℝ) * (n : ℝ) ^ (-β)).trans_le hpbase
  let t := (1 + (n : ℝ) ^ (-(paperAlpha q (r + 1) / 60))) * d ^ 2
  have ht : 0 ≤ t := by dsimp only [t]; positivity
  have hpower := relaxed_colour_joint_power_paper_threshold hqr hn hh hH
    hd ht hpd (le_refl t) s.card hs
  have hc := colour_collision_bound_at_exponents_paper_threshold hqr hn hh hH
    ((Nat.sub_le (Fintype.card W) F.card).trans hw) hs hgap
      (T.card : ℝ) (density D) hsize hpbase
  have he : (n : ℝ) ^ (-(paperAlpha q (r + 1) / 24)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hn1 (by linarith only [paperAlpha_pos hqr])
  have hcollision : ((Fintype.card W - F.card : ℕ) : ℝ) ^ 2 *
      (Fintype.card (Fin n) : ℝ) ^ (Fintype.card W - F.card - 1) ≤
        1 * T.card * density D ^ (2 * s.card) := by
    simp only [Fintype.card_fin]
    exact hc.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right he (Nat.cast_nonneg T.card)) (by positivity))
  have hsecond := extensionColourCount_relative_second_moment s Q T D (r + 1)
    ht hroot hpair (by simpa only [one_add_one_eq_two] using hpower) hcollision
  apply lower_tail_le_eight_ninths_of_second_moment (RandomPermutation.probability I (Fin n))
    (RandomPermutation.eventCount_memLp_two s T (fun f i => extensionColourEvent (Q i) f D))
    (mul_pos hTpos (pow_pos hp _)) (extensionColourCount_mean s Q T D)
  norm_num only [mul_one] at hsecond
  exact hsecond

end Arxiv2411_18291
