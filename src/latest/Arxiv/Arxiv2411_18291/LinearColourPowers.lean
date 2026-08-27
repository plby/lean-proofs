import Arxiv.Arxiv2411_18291.ColourProbabilityNumerics
import Arxiv.Arxiv2411_18291.PaperAlphaGrowth
import Arxiv.Arxiv2411_18291.AbsorberWorkingParameters

/-! # Linear accumulation of small colour-probability errors -/

namespace Arxiv2411_18291

theorem one_add_pow_linear_of_small {x : ℝ} (hx : 0 ≤ x) (M : ℕ) :
    2 * (M : ℝ) * x ≤ 1 → (1 + x) ^ M ≤ 1 + 2 * M * x := by
  induction M with
  | zero => simp
  | succ M ih =>
    intro hsmall
    have hM : 2 * (M : ℝ) * x ≤ 1 := by
      push_cast at hsmall
      nlinarith only [hsmall, hx]
    have hm := mul_le_mul_of_nonneg_right (ih hM) (by linarith only [hx] : 0 ≤ 1 + x)
    have hquad := mul_le_mul_of_nonneg_right hM hx
    rw [pow_succ]
    push_cast
    nlinarith only [hm, hquad]

theorem joint_power_relative_bound_linear {p d t ε : ℝ} (M H : ℕ) (hMH : M ≤ H)
    (hd : 0 ≤ d) (ht0 : 0 ≤ t) (hε : 0 ≤ ε) (hεhalf : ε ≤ 1 / 2)
    (hsmall : 24 * (H : ℝ) * ε ≤ 1)
    (hpd : (1 - ε) * d ≤ p) (ht : t ≤ (1 + ε) * d ^ 2) :
    t ^ M ≤ (1 + 24 * H * ε) * p ^ (2 * M) := by
  have htm := joint_to_marginal_error hd hε hεhalf hpd ht
  have hMsmall : 2 * (M : ℝ) * (12 * ε) ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hMH : (M : ℝ) ≤ H) hε
    nlinarith only [hh, hsmall]
  have hpow := one_add_pow_linear_of_small (by positivity : 0 ≤ 12 * ε) M hMsmall
  have hcoef : (1 + 12 * ε) ^ M ≤ 1 + 24 * H * ε := by
    have hh := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hMH : (M : ℝ) ≤ H) hε
    nlinarith only [hpow, hh]
  have hp2 : 0 ≤ p ^ (2 * M) := by rw [pow_mul]; positivity
  calc
    _ ≤ ((1 + 12 * ε) * p ^ 2) ^ M := pow_le_pow_left₀ ht0 htm _
    _ = (1 + 12 * ε) ^ M * p ^ (2 * M) := by rw [mul_pow, ← pow_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right hcoef hp2

theorem paper_colour_power_coefficient_bound {q r n H : ℕ} (hqr : r + 1 < q)
    (hn : paperSizeThreshold q (r + 1) ≤ n)
    (hH : H ≤ 3 * (2 * q) ^ (r + 1) * (q.choose (r + 1)) ^ 2) :
    (24 * H : ℝ) ≤ (n : ℝ) ^ (paperAlpha q (r + 1) / 24) := by
  have hq : 2 ≤ q := by omega
  have hqR : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hcNat : 24 * H ≤ (4 * q) ^ (2 * q + 2) := by
    calc
      _ ≤ (4 * q) ^ 2 * (4 * q) ^ (2 * q) := Nat.mul_le_mul
        (by nlinarith only [hq] : 24 ≤ (4 * q) ^ 2)
        (hH.trans (paper_exchange_graph_bound (Nat.succ_pos r) hqr))
      _ = _ := by rw [← pow_add]; congr 1; omega
  have hc : (24 * H : ℝ) ≤ (4 * q : ℝ) ^ (2 * q + 2) := by exact_mod_cast hcNat
  have hg := paper_threshold_alpha_rpow_lower hqr hn (s := 2 * q + 2)
    (t := (1 / 24 : ℝ)) (by norm_num) (by push_cast; linarith only [hqR])
  simpa only [div_eq_mul_inv, one_mul] using hc.trans hg

theorem colour_joint_power_bound_paper_threshold {q r n H : ℕ} (hqr : r + 1 < q)
    (hn : paperSizeThreshold q (r + 1) ≤ n) (hh : 1 ≤ H)
    (hH : H ≤ 3 * (2 * q) ^ (r + 1) * (q.choose (r + 1)) ^ 2)
    (p d t : ℝ) (hd : 0 ≤ d) (ht : 0 ≤ t)
    (hpd : (1 - (n : ℝ) ^ (-(paperAlpha q (r + 1) / 12))) * d ≤ p)
    (hpair : t ≤ (1 + (n : ℝ) ^ (-(paperAlpha q (r + 1) / 12))) * d ^ 2)
    (M : ℕ) (hMH : M ≤ H) :
    t ^ M ≤ (1 + (n : ℝ) ^ (-(paperAlpha q (r + 1) / 24))) * p ^ (2 * M) := by
  have hn1 : (1 : ℝ) ≤ n := by
    exact_mod_cast (paperSizeThreshold_one_lt hqr).le.trans hn
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hn1
  have hε := Real.rpow_nonneg hn0.le (-(paperAlpha q (r + 1) / 12))
  have hc := mul_le_mul_of_nonneg_right (paper_colour_power_coefficient_bound hqr hn hH) hε
  have heq : (n : ℝ) ^ (paperAlpha q (r + 1) / 24) *
      (n : ℝ) ^ (-(paperAlpha q (r + 1) / 12)) =
      (n : ℝ) ^ (-(paperAlpha q (r + 1) / 24)) := by
    rw [← Real.rpow_add hn0]
    congr 1
    ring
  rw [heq] at hc
  have hsmall : 24 * (H : ℝ) * (n : ℝ) ^ (-(paperAlpha q (r + 1) / 12)) ≤ 1 :=
    hc.trans (Real.rpow_le_one_of_one_le_of_nonpos hn1 (by linarith only [paperAlpha_pos hqr]))
  have hεhalf : (n : ℝ) ^ (-(paperAlpha q (r + 1) / 12)) ≤ 1 / 2 := by
    have hhR : (1 : ℝ) ≤ H := by exact_mod_cast hh
    have hm := mul_le_mul_of_nonneg_right hhR hε
    nlinarith only [hm, hsmall]
  have hp2 : 0 ≤ p ^ (2 * M) := by rw [pow_mul]; positivity
  exact (joint_power_relative_bound_linear M H hMH hd ht hε hεhalf hsmall hpd hpair).trans
    (mul_le_mul_of_nonneg_right (add_le_add le_rfl hc) hp2)

end Arxiv2411_18291
