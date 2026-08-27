import Arxiv.Arxiv2411_18291.FiniteGoodDensity
import Arxiv.Arxiv2411_18291.FiniteGeneratorCap
import Arxiv.Arxiv2411_18291.PaperReserveGrowth

/-! # Finite observed-density and clique-count conditions for modular selection -/

namespace Arxiv2411_18291

theorem paper_host_error_small {q r n : ℕ} (hqr : r + 1 < q)
    (hn : paperSizeThreshold q (r + 1) ≤ n) :
    2 * (n : ℝ) ^ (-(1 / 10 : ℝ)) ≤ 1 := by
  have hn1 : (1 : ℝ) ≤ n := by
    exact_mod_cast (paperSizeThreshold_one_lt hqr).le.trans hn
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hn1
  have hq : (2 : ℝ) ≤ q := by exact_mod_cast (show 2 ≤ q by omega)
  have hα := (paperAlpha_le_rho hqr).trans (paperRho_le_one_div_36 hqr)
  have hg := paper_threshold_alpha_rpow_lower hqr hn (s := 1)
    (t := 1) (by norm_num) (by push_cast; linarith only [hq])
  simp only [pow_one, mul_one] at hg
  have hb : (2 : ℝ) ≤ (n : ℝ) ^ (1 / 10 : ℝ) :=
    (show (2 : ℝ) ≤ 4 * q by linarith only [hq]).trans
      (hg.trans (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [hα])))
  have hh := mul_le_mul_of_nonneg_right hb (Real.rpow_nonneg hn0.le (-(1 / 10 : ℝ)))
  rw [← Real.rpow_add hn0, add_neg_cancel, Real.rpow_zero] at hh
  exact hh

theorem paper_host_density_bounds {q r n : ℕ} (hqr : r + 1 < q)
    (hn : paperSizeThreshold q (r + 1) ≤ n) (K : Hypergraph (Fin n) (r + 1))
    (hd : |density K - (n : ℝ) ^ (-paperAlpha q (r + 1))| ≤
      (n : ℝ) ^ (-(1 / 10 : ℝ)) * (n : ℝ) ^ (-paperAlpha q (r + 1))) :
    (1 / 2 : ℝ) * (n : ℝ) ^ (-paperAlpha q (r + 1)) ≤ density K ∧
      density K ≤ 2 * (n : ℝ) ^ (-paperAlpha q (r + 1)) := by
  have he := paper_host_error_small hqr hn
  have hp := Real.rpow_nonneg (Nat.cast_nonneg n) (-paperAlpha q (r + 1))
  have hm := mul_le_mul_of_nonneg_right he hp
  obtain ⟨hlo, hhi⟩ := abs_le.mp hd
  constructor <;> nlinarith only [hm, hlo, hhi, hp]

theorem modular_host_clique_size_paper_threshold {q r n : ℕ} (hqr : r + 1 < q)
    (hn : paperSizeThreshold q (r + 1) ≤ n) (K : Hypergraph (Fin n) (r + 1))
    (hd : |density K - (n : ℝ) ^ (-paperAlpha q (r + 1))| ≤
      (n : ℝ) ^ (-(1 / 10 : ℝ)) * (n : ℝ) ^ (-paperAlpha q (r + 1))) :
    (q : ℝ) ≤ (n : ℝ) ^ (-(1 / 10 : ℝ)) * (n * density K ^ q.choose (r + 1)) := by
  have hn1 : (1 : ℝ) ≤ n := by
    exact_mod_cast (paperSizeThreshold_one_lt hqr).le.trans hn
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hn1
  have hq : (2 : ℝ) ≤ q := by exact_mod_cast (show 2 ≤ q by omega)
  have hp := good_reference_density_power_paper_threshold hqr hn le_rfl K K hd
    (Finset.Subset.refl _) (by
      simp only [Finset.sdiff_self, Finset.card_empty, Nat.cast_zero]
      positivity)
  have hα := (paperAlpha_le_rho hqr).trans (paperRho_le_one_div_36 hqr)
  have hαK : paperAlpha q (r + 1) * q.choose (r + 1) ≤ 1 / 36 :=
    (mul_le_mul_of_nonneg_right (paperAlpha_le_rho hqr) (Nat.cast_nonneg _)).trans
      (paperRho_mul_choose_le hqr)
  have hg := paper_threshold_alpha_rpow_lower hqr hn (s := 1)
    (t := 1) (by norm_num) (by push_cast; linarith only [hq])
  simp only [pow_one, mul_one] at hg
  have hb : (2 * q : ℝ) ≤
      (n : ℝ) ^ (1 - (1 / 10 : ℝ) - paperAlpha q (r + 1) * q.choose (r + 1)) :=
    (show (2 * q : ℝ) ≤ 4 * q by linarith only [hq]).trans (hg.trans
      (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [hα, hαK])))
  have heq := clique_count_scale hn0 1 (paperAlpha q (r + 1)) (1 / 10) (q.choose (r + 1))
  simp only [one_mul, one_pow] at heq
  calc
    _ ≤ (1 / 2 : ℝ) *
        (n : ℝ) ^ (1 - (1 / 10 : ℝ) - paperAlpha q (r + 1) * q.choose (r + 1)) :=
      by linarith only [hb]
    _ = (n : ℝ) ^ (-(1 / 10 : ℝ)) *
        (n * ((1 / 2 : ℝ) * ((n : ℝ) ^ (-paperAlpha q (r + 1))) ^ q.choose (r + 1))) := by
      rw [← heq]
      ring
    _ ≤ _ := by gcongr

end Arxiv2411_18291
