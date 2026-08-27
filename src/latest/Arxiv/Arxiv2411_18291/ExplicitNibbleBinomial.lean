import Arxiv.Arxiv2411_18291.ExplicitBoostBinomial
import Arxiv.Arxiv2411_18291.ExplicitNibbleMargins

/-! # Finite binomial and leave-scale conversions for the nibble -/

namespace Arxiv2411_18291

theorem paper_threshold_choose_ge_half_power {q r n d : ℕ} (hr : 1 ≤ r) (hqr : r < q)
    (hn : paperSizeThreshold q r ≤ n) (hd : d ≤ q) :
    (n : ℝ) ^ d / (2 * d.factorial) ≤ n.choose d := by
  have hboost := (boost_threshold_le_paper_threshold hqr).trans hn
  obtain ⟨hc, _, hchoose⟩ := explicit_boost_binomial_numerics (by omega : 2 ≤ q) hboost
  have hpow : (0 : ℝ) ≤ (n : ℝ) ^ d / d.factorial := by positivity
  calc
    _ = (1 / 2 : ℝ) * ((n : ℝ) ^ d / d.factorial) := by ring
    _ ≤ (1 - (n : ℝ) ^ (-(2 / 5 : ℝ))) * ((n : ℝ) ^ d / d.factorial) :=
      mul_le_mul_of_nonneg_right (by linarith only [hc]) hpow
    _ = (1 - (n : ℝ) ^ (-(2 / 5 : ℝ))) * (n : ℝ) ^ d / d.factorial := by ring
    _ ≤ _ := hchoose d hd

theorem paper_nibble_floor_eq_four_rho {q r : ℕ} (hqr : r < q) :
    (1 / (9 * q.choose r) : ℝ) = 4 * ((q.choose r : ℝ) * paperRho q r) := by
  have hk : (q.choose r : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hqr.le).ne'
  unfold paperRho
  field_simp
  ring

theorem paper_nibble_leave_scale {q r n : ℕ} (hr : 1 ≤ r) (hqr : r < q)
    (hn : paperSizeThreshold q r ≤ n) :
    3 * (n : ℝ) ^ (-(1 / (9 * q.choose r) : ℝ)) ≤
      (n : ℝ) ^ (-(3 * q.choose r * paperRho q r)) := by
  have hK : (1 : ℝ) ≤ q.choose r := by exact_mod_cast Nat.choose_pos hqr.le
  have hρ := paperRho_pos hqr
  have hmul := mul_le_mul_of_nonneg_right hK hρ.le
  have hgap : paperRho q r + (-(1 / (9 * q.choose r) : ℝ)) ≤
      -(3 * q.choose r * paperRho q r) := by
    rw [paper_nibble_floor_eq_four_rho hqr]
    nlinarith only [hmul]
  simpa only [pow_zero, Nat.factorial_zero, Nat.cast_one, Nat.cast_ofNat, mul_one] using
    paper_nibble_scaled_monomial (C := 3) (j := 0) (d := 0) hr hqr hn
      (by norm_num) (by norm_num) (by omega) hgap

end Arxiv2411_18291
