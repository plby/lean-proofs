import Arxiv.Arxiv2411_18291.FiniteCliqueColours
import Arxiv.Arxiv2411_18291.RelaxedColourNumerics

/-! # Clique colours under the squared saturation error of capped generators -/

open Finset MeasureTheory

noncomputable section

namespace Arxiv2411_18291

theorem clique_colour_estimates_relaxed_paper_threshold {q r n h : ℕ}
    [MeasurableSpace (Equiv.Perm (Fin n))]
    [MeasurableSingletonClass (Equiv.Perm (Fin n))]
    (hqr : r + 1 < q) (hn : paperSizeThreshold q (r + 1) ≤ n)
    (hqh : q.choose (r + 1) ≤ h)
    (hH : h ≤ 3 * (2 * q) ^ (r + 1) * (q.choose (r + 1)) ^ 2)
    (K : Hypergraph (Fin n) (r + 1))
    (hT : IsTypical K ((n : ℝ) ^ (-(1 / 10 : ℝ))) h)
    (hd : |density K - (n : ℝ) ^ (-paperAlpha q (r + 1))| ≤
      (n : ℝ) ^ (-(1 / 10 : ℝ)) * (n : ℝ) ^ (-paperAlpha q (r + 1)))
    (D : Finset (Block (Fin n) q)) (hD : D ⊆ cliqueFamily K q)
    (hloss : (((cliqueFamily K q) \ D).card : ℝ) ≤
      ((n : ℝ) ^ (-(paperAlpha q (r + 1) / 60))) ^ 2 * (cliqueFamily K q).card) :
    (1 / 4 : ℝ) * (n : ℝ) ^ (-(paperAlpha q (r + 1) * q.choose (r + 1))) ≤ density D ∧
      (1 - (n : ℝ) ^ (-(paperAlpha q (r + 1) / 60))) *
        density K ^ q.choose (r + 1) ≤ density D ∧
      ∀ j < r + 1, ∀ P : IntersectingBlockPair (Fin n) q q j,
        (PMF.uniformOfFintype (Equiv.Perm (Fin n))).toMeasure.real
          {σ | P.val.1 ∈ mapGraph σ.toEmbedding D ∧ P.val.2 ∈ mapGraph σ.toEmbedding D} ≤
          (1 + (n : ℝ) ^ (-(paperAlpha q (r + 1) / 60))) *
            (density K ^ q.choose (r + 1)) ^ 2 := by
  have hn1 : (1 : ℝ) ≤ n := by
    exact_mod_cast (paperSizeThreshold_one_lt hqr).le.trans hn
  have hn0 : (0 : ℝ) < n := zero_lt_one.trans_le hn1
  let δ := (n : ℝ) ^ (-(paperAlpha q (r + 1) / 60))
  have hδ0 : 0 ≤ δ := Real.rpow_nonneg hn0.le _
  have hδ := relaxed_colour_error_le_eighth_paper_threshold hqr hn
    ((Nat.choose_pos hqr.le).trans_le hqh) hH
  change δ ≤ 1 / 8 at hδ
  have hε1 : δ ^ 2 ≤ 1 := by nlinarith only [hδ0, hδ]
  have hεold : (n : ℝ) ^ (-(paperAlpha q (r + 1) / 10)) ≤ δ ^ 2 := by
    dsimp only [δ]
    rw [← Real.rpow_mul_natCast hn0.le]
    apply Real.rpow_le_rpow_of_exponent_le hn1
    norm_num
    linarith only [paperAlpha_pos hqr]
  have hqn : q ≤ Fintype.card (Fin n) := by
    have hαhi := (paperAlpha_le_rho hqr).trans (paperRho_le_one_div_36 hqr)
    have hh := paper_quadratic_size_margin hqr hn (by linarith only [hαhi] :
      paperAlpha q (r + 1) ≤ 1)
    rw [Real.rpow_one] at hh
    have hq : (2 : ℝ) ≤ q := by exact_mod_cast (show 2 ≤ q by omega)
    simp only [Fintype.card_fin]
    exact_mod_cast (by nlinarith only [hq, hh] : (q : ℝ) ≤ n)
  have hc := (cliqueFamily_relative_error_paper_threshold hqr hn hqh K hT hd).trans
    (mul_le_mul_of_nonneg_right hεold
      (cliqueMainTerm_nonneg (Nat.cast_nonneg n) (density_nonneg K) _ _ _))
  have hgood := clique_subfamily_density_lower K D hD hqn hε1
    (by simpa only [Fintype.card_fin] using hc) hloss
  have h2 : 2 * δ ^ 2 ≤ δ := by nlinarith only [hδ0, hδ]
  have hd0 := pow_nonneg (density_nonneg K) (q.choose (r + 1))
  have hmarg : (1 - δ) * density K ^ q.choose (r + 1) ≤ density D :=
    (mul_le_mul_of_nonneg_right (sub_le_sub_left h2 1) hd0).trans hgood
  have hhalf : density K ^ q.choose (r + 1) / 2 ≤ density D := by
    have hm := mul_le_mul_of_nonneg_right hδ hd0
    nlinarith only [hmarg, hm, hd0]
  refine ⟨?_, hmarg, ?_⟩
  · have hzero : ((K \ K).card : ℝ) ≤
        (n : ℝ) ^ (-(paperAlpha q (r + 1) / 10)) * K.card := by
      rw [Finset.sdiff_self, Finset.card_empty, Nat.cast_zero]
      positivity
    have hp := good_reference_density_power_paper_threshold hqr hn
      (s := q.choose (r + 1)) le_rfl K K hd (Subset.refl K) hzero
    rw [← Real.rpow_mul_natCast hn0.le, neg_mul] at hp
    linarith only [hp, hhalf]
  · intro j hj P
    have hzero : (((cliqueFamily K q) \ cliqueFamily K q).card : ℝ) ≤
        (n : ℝ) ^ (-(paperAlpha q (r + 1) / 10)) * (cliqueFamily K q).card := by
      rw [Finset.sdiff_self, Finset.card_empty, Nat.cast_zero]
      positivity
    have hpair := (clique_colour_estimates_paper_threshold hqr hn hqh K hT hd
      (cliqueFamily K q) (Subset.refl _) hzero).2.2 j hj P
    have hsub : {σ : Equiv.Perm (Fin n) |
        P.val.1 ∈ mapGraph σ.toEmbedding D ∧ P.val.2 ∈ mapGraph σ.toEmbedding D} ⊆
        {σ | P.val.1 ∈ mapGraph σ.toEmbedding (cliqueFamily K q) ∧
          P.val.2 ∈ mapGraph σ.toEmbedding (cliqueFamily K q)} :=
      fun σ hσ => ⟨mapGraph_mono σ.toEmbedding hD hσ.1, mapGraph_mono σ.toEmbedding hD hσ.2⟩
    have he : (n : ℝ) ^ (-(paperAlpha q (r + 1) / 12)) ≤ δ :=
      Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [paperAlpha_pos hqr])
    exact (measureReal_mono (μ := (PMF.uniformOfFintype (Equiv.Perm (Fin n))).toMeasure)
      hsub).trans (hpair.trans
        (mul_le_mul_of_nonneg_right (add_le_add (le_refl 1) he) (sq_nonneg _)))

end Arxiv2411_18291
