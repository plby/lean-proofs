import Arxiv.Arxiv2411_18291.FinitePermutationPairs
import Arxiv.Arxiv2411_18291.CliqueSubfamilyDensity

/-! # Finite colour estimates for the unsaturated clique family -/

open Finset MeasureTheory

noncomputable section

namespace Arxiv2411_18291

theorem cliqueFamily_relative_error_paper_threshold {q r n h : ℕ}
    (hqr : r + 1 < q) (hn : paperSizeThreshold q (r + 1) ≤ n)
    (hqh : q.choose (r + 1) ≤ h) (K : Hypergraph (Fin n) (r + 1))
    (hT : IsTypical K ((n : ℝ) ^ (-(1 / 10 : ℝ))) h)
    (hd : |density K - (n : ℝ) ^ (-paperAlpha q (r + 1))| ≤
      (n : ℝ) ^ (-(1 / 10 : ℝ)) * (n : ℝ) ^ (-paperAlpha q (r + 1))) :
    |((cliqueFamily K q).card : ℝ) - cliqueMainTerm n (density K) q (r + 1) 0| ≤
      (n : ℝ) ^ (-(paperAlpha q (r + 1) / 10)) *
        cliqueMainTerm n (density K) q (r + 1) 0 := by
  have hc0 := Real.rpow_nonneg (Nat.cast_nonneg n) (-(1 / 10 : ℝ))
  have hsize : (q : ℝ) ≤ (2 * (n : ℝ) ^ (-(1 / 10 : ℝ)) -
      (n : ℝ) ^ (-(1 / 10 : ℝ))) * (Fintype.card (Fin n) * density K ^ q.choose (r + 1)) := by
    rw [Fintype.card_fin, show 2 * (n : ℝ) ^ (-(1 / 10 : ℝ)) -
      (n : ℝ) ^ (-(1 / 10 : ℝ)) = (n : ℝ) ^ (-(1 / 10 : ℝ)) by ring]
    exact modular_host_clique_size_paper_threshold hqr hn K hd
  have hc := hT.cliqueFamily_relative hqh (by linarith only [hc0])
    (by positivity) (paper_host_error_small hqr hn) hsize
  simp only [Fintype.card_fin] at hc
  have herr := generator_count_error_paper_threshold hqr hn
  have hε := Real.rpow_nonneg (Nat.cast_nonneg n) (-(paperAlpha q (r + 1) / 10))
  exact hc.trans (mul_le_mul_of_nonneg_right (by linarith only [herr, hε])
    (cliqueMainTerm_nonneg (Nat.cast_nonneg n) (density_nonneg K) q (r + 1) 0))

theorem clique_colour_estimates_paper_threshold {q r n h : ℕ} (hqr : r + 1 < q)
    (hn : paperSizeThreshold q (r + 1) ≤ n) (hqh : q.choose (r + 1) ≤ h)
    (K : Hypergraph (Fin n) (r + 1))
    (hT : IsTypical K ((n : ℝ) ^ (-(1 / 10 : ℝ))) h)
    (hd : |density K - (n : ℝ) ^ (-paperAlpha q (r + 1))| ≤
      (n : ℝ) ^ (-(1 / 10 : ℝ)) * (n : ℝ) ^ (-paperAlpha q (r + 1)))
    (D : Finset (Block (Fin n) q)) (hD : D ⊆ cliqueFamily K q)
    (hloss : (((cliqueFamily K q) \ D).card : ℝ) ≤
      (n : ℝ) ^ (-(paperAlpha q (r + 1) / 10)) * (cliqueFamily K q).card) :
    (1 / 4 : ℝ) * (n : ℝ) ^ (-(paperAlpha q (r + 1) * q.choose (r + 1))) ≤ density D ∧
      (1 - (n : ℝ) ^ (-(paperAlpha q (r + 1) / 12))) *
        density K ^ q.choose (r + 1) ≤ density D ∧
      ∀ [MeasurableSpace (Equiv.Perm (Fin n))]
        [MeasurableSingletonClass (Equiv.Perm (Fin n))],
      ∀ j < r + 1, ∀ P : IntersectingBlockPair (Fin n) q q j,
        (PMF.uniformOfFintype (Equiv.Perm (Fin n))).toMeasure.real
          {σ | P.val.1 ∈ mapGraph σ.toEmbedding D ∧ P.val.2 ∈ mapGraph σ.toEmbedding D} ≤
          (1 + (n : ℝ) ^ (-(paperAlpha q (r + 1) / 12))) *
            (density K ^ q.choose (r + 1)) ^ 2 := by
  have hn1 : (1 : ℝ) ≤ n := by
    exact_mod_cast (paperSizeThreshold_one_lt hqr).le.trans hn
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hn1
  have hq : (2 : ℝ) ≤ q := by exact_mod_cast (show 2 ≤ q by omega)
  have hα := paperAlpha_pos hqr
  have hαhi := (paperAlpha_le_rho hqr).trans (paperRho_le_one_div_36 hqr)
  have hqn : q ≤ Fintype.card (Fin n) := by
    have hh := paper_quadratic_size_margin hqr hn (by linarith only [hαhi] :
      paperAlpha q (r + 1) ≤ 1)
    rw [Real.rpow_one] at hh
    simp only [Fintype.card_fin]
    exact_mod_cast (by nlinarith only [hq, hh] : (q : ℝ) ≤ n)
  have hε1 : (n : ℝ) ^ (-(paperAlpha q (r + 1) / 10)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hn1 (by linarith only [hα])
  have hgood := clique_subfamily_density_lower K D hD hqn hε1
    (by simpa only [Fintype.card_fin] using
      cliqueFamily_relative_error_paper_threshold hqr hn hqh K hT hd) hloss
  have h2 : 2 * (n : ℝ) ^ (-(paperAlpha q (r + 1) / 10)) ≤
      (n : ℝ) ^ (-(paperAlpha q (r + 1) / 12)) := by
    have hg := paper_threshold_alpha_rpow_lower hqr hn (s := 1)
      (t := (1 / 60 : ℝ)) (by norm_num) (by push_cast; linarith only [hq])
    have hc : (2 : ℝ) ≤ (n : ℝ) ^ (paperAlpha q (r + 1) / 60) := by
      have hh : (2 : ℝ) ≤ (4 * q : ℝ) ^ 1 := by simp only [pow_one]; linarith only [hq]
      simpa only [div_eq_mul_inv, one_mul] using hh.trans hg
    have hm := mul_le_mul_of_nonneg_right hc
      (Real.rpow_nonneg hn0.le (-(paperAlpha q (r + 1) / 10)))
    rw [← Real.rpow_add hn0] at hm
    rwa [show paperAlpha q (r + 1) / 60 + -(paperAlpha q (r + 1) / 10) =
      -(paperAlpha q (r + 1) / 12) by ring] at hm
  have hsmall : (n : ℝ) ^ (-(paperAlpha q (r + 1) / 12)) ≤ 1 / 2 := by
    have hg := paper_threshold_alpha_rpow_lower hqr hn (s := 1)
      (t := (1 / 12 : ℝ)) (by norm_num) (by push_cast; linarith only [hq])
    have hc : (2 : ℝ) ≤ (n : ℝ) ^ (paperAlpha q (r + 1) / 12) := by
      have hh : (2 : ℝ) ≤ (4 * q : ℝ) ^ 1 := by simp only [pow_one]; linarith only [hq]
      simpa only [div_eq_mul_inv, one_mul] using hh.trans hg
    have hm := mul_le_mul_of_nonneg_right hc
      (Real.rpow_nonneg hn0.le (-(paperAlpha q (r + 1) / 12)))
    rw [← Real.rpow_add hn0, add_neg_cancel, Real.rpow_zero] at hm
    linarith only [hm]
  have hd0 := pow_nonneg (density_nonneg K) (q.choose (r + 1))
  have hmarg : (1 - (n : ℝ) ^ (-(paperAlpha q (r + 1) / 12))) *
      density K ^ q.choose (r + 1) ≤ density D :=
    (mul_le_mul_of_nonneg_right (sub_le_sub_left h2 1) hd0).trans hgood
  have hhalf : density K ^ q.choose (r + 1) / 2 ≤ density D := by
    have hm := mul_le_mul_of_nonneg_right hsmall hd0
    linarith only [hmarg, hm]
  refine ⟨?_, hmarg, ?_⟩
  · have hlossK : ((K \ K).card : ℝ) ≤
        (n : ℝ) ^ (-(paperAlpha q (r + 1) / 10)) * K.card := by
      rw [Finset.sdiff_self, Finset.card_empty, Nat.cast_zero]
      positivity
    have hp := good_reference_density_power_paper_threshold hqr hn
      (s := q.choose (r + 1)) le_rfl K K hd (Subset.refl K) hlossK
    rw [← Real.rpow_mul_natCast hn0.le, neg_mul] at hp
    linarith only [hp, hhalf]
  · intro _ _ j hj P
    have hp := permuted_clique_pair_probability_paper_threshold hqr hn le_rfl hqh
      K hT hd P hj D D hD hD
    rw [mul_comm 2, pow_mul] at hp
    have hg := paper_threshold_alpha_rpow_lower hqr hn (s := 2)
      (t := (1 / 12 : ℝ)) (by norm_num) (by push_cast; linarith only [hq])
    have hc : (16 : ℝ) ≤ (n : ℝ) ^ (paperAlpha q (r + 1) / 12) := by
      have hh : (16 : ℝ) ≤ (4 * q : ℝ) ^ 2 := by nlinarith only [hq]
      simpa only [div_eq_mul_inv, one_mul] using hh.trans hg
    have hm := mul_le_mul_of_nonneg_right hc
      (Real.rpow_nonneg hn0.le (-(paperAlpha q (r + 1) / 6)))
    rw [← Real.rpow_add hn0,
      show paperAlpha q (r + 1) / 12 + -(paperAlpha q (r + 1) / 6) =
        -(paperAlpha q (r + 1) / 12) by ring] at hm
    exact hp.trans (mul_le_mul_of_nonneg_right (add_le_add le_rfl hm) (sq_nonneg _))

end Arxiv2411_18291
