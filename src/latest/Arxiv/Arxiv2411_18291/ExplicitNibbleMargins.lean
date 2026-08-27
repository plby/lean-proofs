import Arxiv.Arxiv2411_18291.ExplicitNibbleGrowth
import Arxiv.Arxiv2411_18291.AsymptoticNibbleExponents

/-! # Finite power margins for the nibble's numerical conditions -/

namespace Arxiv2411_18291

theorem paper_nibble_scaled_monomial {q r n C j d : ℕ} (hr : 1 ≤ r)
    (hqr : r < q) (hn : paperSizeThreshold q r ≤ n)
    (hC : C ≤ 2 ^ 24) (hj : j ≤ 6) (hd : d ≤ q) {u v : ℝ}
    (hgap : paperRho q r + u ≤ v) :
    ((C : ℝ) * (q.choose r : ℝ) ^ j * d.factorial) * (n : ℝ) ^ u ≤ (n : ℝ) ^ v := by
  have hn1 : (1 : ℝ) ≤ n := by
    exact_mod_cast (paperSizeThreshold_one_lt hqr).le.trans hn
  have hc : (C : ℝ) * (q.choose r : ℝ) ^ j * d.factorial ≤
      (n : ℝ) ^ paperRho q r := by
    simpa only [pow_zero, mul_one] using
      paper_threshold_nibble_monomial hr hqr hn hC (by norm_num : 0 ≤ 2) hj hd
  simpa only [one_mul] using scaled_rpow_le_of_coefficient_bound hn1 zero_le_one
    (by simpa only [one_mul] using hc) hgap

theorem rpow_margin_of_density_lower {x C c g α γ t u : ℝ} (hx : 1 ≤ x)
    (hc : 0 < c) (hg : x ^ γ / c ≤ g) (hC : C * c ≤ x ^ t)
    (m : ℕ) (hgap : t + u ≤ γ - (m : ℝ) * α) :
    C * x ^ u ≤ (x ^ (-α)) ^ m * g := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hcoef : C ≤ (1 / c) * x ^ t := by
    have hh := (le_div_iff₀ hc).mpr hC
    simpa only [one_div, div_eq_mul_inv, mul_comm, mul_one, one_mul] using hh
  have hscaled := scaled_rpow_le_of_coefficient_bound hx (by positivity) hcoef hgap
  calc
    _ ≤ (1 / c) * x ^ (γ - (m : ℝ) * α) := hscaled
    _ = (x ^ (-α)) ^ m * (x ^ γ / c) := by
      rw [show x ^ γ / c = (1 / c) * x ^ γ by ring, rpow_nat_decay_mul hx0]
    _ ≤ _ := mul_le_mul_of_nonneg_left hg (by positivity)

theorem paper_nibble_floor_gaps {q r : ℕ} (hqr : r < q) (hk : 3 ≤ q.choose r) :
    let β : ℝ := 1 / (9 * q.choose r)
    paperRho q r + 2 * β ≤ 1 / 9 ∧
      paperRho q r + β ≤ 1 / 9 ∧ paperRho q r ≤ 2 * β := by
  dsimp only
  have hkR : (3 : ℝ) ≤ q.choose r := by exact_mod_cast hk
  have hkpos : (0 : ℝ) < q.choose r := by linarith only [hkR]
  have hβsmall : (1 / (9 * q.choose r) : ℝ) ≤ 1 / 27 := by
    apply one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 27)
    linarith only [hkR]
  have hρ := paperRho_le_one_div_36 hqr
  refine ⟨by linarith only [hρ, hβsmall], by linarith only [hρ, hβsmall], ?_⟩
  have hρK := paperRho_mul_choose_le hqr
  have hdiv : paperRho q r ≤ 2 / (9 * q.choose r) := by
    apply (le_div_iff₀ (by positivity)).mpr
    nlinarith only [hρK]
  simpa only [div_eq_mul_inv, one_mul] using hdiv

end Arxiv2411_18291
