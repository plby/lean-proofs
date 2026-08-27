import Arxiv.Arxiv2411_18291.FiniteGoodDensity
import Arxiv.Arxiv2411_18291.RelaxedColourNumerics

/-! # Good-host density powers through the full exchange size

The relaxed deletion error still has `8*H*delta <= 1` at n0. Thus every
density power through H retains half the reference value, without a
factor exponential in the number of edges.
-/

noncomputable section

namespace Arxiv2411_18291

theorem good_reference_density_power_relaxed_paper_threshold {q r n H s : ℕ}
    (hqr : r + 1 < q) (hn : paperSizeThreshold q (r + 1) ≤ n) (hh : 1 ≤ H)
    (hH : H ≤ 3 * (2 * q) ^ (r + 1) * (q.choose (r + 1)) ^ 2)
    (hs : s ≤ H) (K G : Hypergraph (Fin n) (r + 1))
    (hd : |density K - (n : ℝ) ^ (-paperAlpha q (r + 1))| ≤
      (n : ℝ) ^ (-(1 / 10 : ℝ)) * (n : ℝ) ^ (-paperAlpha q (r + 1)))
    (hGK : G ⊆ K)
    (hloss : ((K \ G).card : ℝ) ≤
      (n : ℝ) ^ (-(paperAlpha q (r + 1) / 60)) * K.card) :
    (1 / 2 : ℝ) * ((n : ℝ) ^ (-paperAlpha q (r + 1))) ^ s ≤ density G ^ s := by
  have hn1 : (1 : ℝ) ≤ n := by
    exact_mod_cast (paperSizeThreshold_one_lt hqr).le.trans hn
  have hαupper := (paperAlpha_le_rho hqr).trans (paperRho_le_one_div_36 hqr)
  have hδε : (n : ℝ) ^ (-(1 / 10 : ℝ)) ≤
      (n : ℝ) ^ (-(paperAlpha q (r + 1) / 60)) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [hαupper])
  have hε : 0 ≤ (n : ℝ) ^ (-(paperAlpha q (r + 1) / 60)) :=
    Real.rpow_nonneg (Nat.cast_nonneg n) _
  have heighth := relaxed_colour_error_le_eighth_paper_threshold hqr hn hh hH
  have hsmall : 6 * (n : ℝ) ^ (-(paperAlpha q (r + 1) / 60)) ≤ 1 :=
    by linarith only [heighth]
  have hscaled : 6 * (s : ℝ) * (n : ℝ) ^ (-(paperAlpha q (r + 1) / 60)) ≤ 1 := by
    calc
      _ ≤ 8 * (H : ℝ) * (n : ℝ) ^ (-(paperAlpha q (r + 1) / 60)) :=
        mul_le_mul_of_nonneg_right
          (by exact_mod_cast (show 6 * s ≤ 8 * H by omega)) hε
      _ ≤ _ := relaxed_colour_error_small_paper_threshold hqr hn hH
  exact density_pow_lower_of_small_relative_errors (Real.rpow_nonneg (Nat.cast_nonneg n) _)
    hε hδε hsmall hscaled hd hGK hloss

theorem good_reference_density_lower_relaxed_paper_threshold {q r n H : ℕ}
    (hqr : r + 1 < q) (hn : paperSizeThreshold q (r + 1) ≤ n) (hh : 1 ≤ H)
    (hH : H ≤ 3 * (2 * q) ^ (r + 1) * (q.choose (r + 1)) ^ 2)
    (K G : Hypergraph (Fin n) (r + 1))
    (hd : |density K - (n : ℝ) ^ (-paperAlpha q (r + 1))| ≤
      (n : ℝ) ^ (-(1 / 10 : ℝ)) * (n : ℝ) ^ (-paperAlpha q (r + 1)))
    (hGK : G ⊆ K)
    (hloss : ((K \ G).card : ℝ) ≤
      (n : ℝ) ^ (-(paperAlpha q (r + 1) / 60)) * K.card) :
    (1 / 2 : ℝ) * (n : ℝ) ^ (-paperAlpha q (r + 1)) ≤ density G := by
  simpa only [pow_one] using good_reference_density_power_relaxed_paper_threshold
    hqr hn hh hH (s := 1) hh K G hd hGK hloss

end Arxiv2411_18291
