import Arxiv.Arxiv2411_18291.LinearColourPowers

/-! # Colour moments with the relaxed error of the edge-capped generators -/

namespace Arxiv2411_18291

theorem joint_to_marginal_error_small {p d t ε : ℝ} (hd : 0 ≤ d) (hε : 0 ≤ ε)
    (hεsmall : ε ≤ 1 / 8) (hpd : (1 - ε) * d ≤ p)
    (ht : t ≤ (1 + ε) * d ^ 2) : t ≤ (1 + 4 * ε) * p ^ 2 := by
  have hpoly : 0 ≤ ε * (1 - 7 * ε + 4 * ε ^ 2) :=
    mul_nonneg hε (by nlinarith only [hεsmall, sq_nonneg ε])
  have hcoef : 1 + ε ≤ (1 + 4 * ε) * (1 - ε) ^ 2 := by nlinarith only [hpoly]
  have hs := pow_le_pow_left₀ (mul_nonneg (by linarith only [hεsmall]) hd) hpd 2
  calc
    t ≤ (1 + ε) * d ^ 2 := ht
    _ ≤ ((1 + 4 * ε) * (1 - ε) ^ 2) * d ^ 2 :=
      mul_le_mul_of_nonneg_right hcoef (sq_nonneg d)
    _ = (1 + 4 * ε) * ((1 - ε) * d) ^ 2 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hs (by positivity)

theorem joint_power_le_twice {p d t ε : ℝ} (M H : ℕ) (hMH : M ≤ H)
    (hd : 0 ≤ d) (ht0 : 0 ≤ t) (hε : 0 ≤ ε) (hεsmall : ε ≤ 1 / 8)
    (hsmall : 8 * (H : ℝ) * ε ≤ 1)
    (hpd : (1 - ε) * d ≤ p) (ht : t ≤ (1 + ε) * d ^ 2) :
    t ^ M ≤ 2 * p ^ (2 * M) := by
  have htm := joint_to_marginal_error_small hd hε hεsmall hpd ht
  have hMsmall : 2 * (M : ℝ) * (4 * ε) ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hMH : (M : ℝ) ≤ H) hε
    nlinarith only [hh, hsmall]
  have hp := one_add_pow_linear_of_small (by positivity : 0 ≤ 4 * ε) M hMsmall
  have hcoef : (1 + 4 * ε) ^ M ≤ 2 := by linarith only [hp, hMsmall]
  calc
    _ ≤ ((1 + 4 * ε) * p ^ 2) ^ M := pow_le_pow_left₀ ht0 htm _
    _ = (1 + 4 * ε) ^ M * p ^ (2 * M) := by rw [mul_pow, ← pow_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right hcoef (by rw [pow_mul]; positivity)

theorem exchange_eight_square_bound {q r H : ℕ} (hqr : r + 1 < q)
    (hH : H ≤ 3 * (2 * q) ^ (r + 1) * (q.choose (r + 1)) ^ 2) :
    (8 * H) ^ 2 ≤ (4 * q) ^ (3 * q) := by
  by_cases hq : 3 ≤ q
  · have hk : (q.choose (r + 1)) ^ 4 ≤ 16 ^ q := by
      calc
        _ ≤ (2 ^ q) ^ 4 := Nat.pow_le_pow_left (Nat.choose_le_two_pow _ _) 4
        _ = 16 ^ q := by rw [← pow_mul, mul_comm q 4, pow_mul]; norm_num
    have hbase : 1 ≤ 2 * q := by omega
    have hpow := Nat.pow_le_pow_left (Nat.mul_le_mul_left 8 hH) 2
    have hmul : (8 * H) ^ 2 * (2 * q) ^ 2 ≤
        576 * (2 * q) ^ (2 * q) * 16 ^ q := by
      calc
        _ ≤ (8 * (3 * (2 * q) ^ (r + 1) * (q.choose (r + 1)) ^ 2)) ^ 2 *
            (2 * q) ^ 2 := Nat.mul_le_mul_right _ hpow
        _ = 576 * ((2 * q) ^ (2 * (r + 1)) * (2 * q) ^ 2) *
            (q.choose (r + 1)) ^ 4 := by
          rw [show 2 * (r + 1) = (r + 1) * 2 by omega, pow_mul]
          ring
        _ = 576 * (2 * q) ^ (2 * (r + 1) + 2) *
            (q.choose (r + 1)) ^ 4 := by rw [pow_add]
        _ ≤ _ := Nat.mul_le_mul (Nat.mul_le_mul_left _
          (Nat.pow_le_pow_right hbase (by omega))) hk
    have hcoef : 144 ≤ q ^ (q + 2) :=
      (by norm_num : 144 ≤ 3 ^ 5).trans
        ((Nat.pow_le_pow_left hq 5).trans (Nat.pow_le_pow_right (by omega) (by omega)))
    have hfinal : 576 * (2 * q) ^ (2 * q) * 16 ^ q ≤
        (4 * q) ^ (3 * q) * (2 * q) ^ 2 := by
      calc
        _ ≤ (4 * q ^ (q + 2)) * (2 * q) ^ (2 * q) * 16 ^ q :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by omega : 576 ≤ 4 * q ^ (q + 2)))
        _ = _ := by
          rw [pow_add, pow_mul, pow_mul]
          simp only [mul_pow]
          rw [← mul_pow, ← mul_pow]
          ring_nf
          have heq : (4 : ℕ) ^ q * 16 ^ q = 64 ^ q := by rw [← mul_pow]; norm_num
          have hh := congrArg (fun x : ℕ => q ^ 2 * q ^ (q * 3) * x * 4) heq
          simpa only [mul_assoc] using hh
    exact (mul_le_mul_iff_left₀ (by positivity : 0 < (2 * q) ^ 2)).mp (hmul.trans hfinal)
  · have hq2 : q = 2 := by omega
    have hr : r = 0 := by omega
    subst q r
    norm_num at hH ⊢
    have hh := Nat.pow_le_pow_left (Nat.mul_le_mul_left 8 hH) 2
    norm_num at hh
    omega

theorem relaxed_colour_error_small_paper_threshold {q r n H : ℕ}
    (hqr : r + 1 < q) (hn : paperSizeThreshold q (r + 1) ≤ n)
    (hH : H ≤ 3 * (2 * q) ^ (r + 1) * (q.choose (r + 1)) ^ 2) :
    8 * (H : ℝ) * (n : ℝ) ^ (-(paperAlpha q (r + 1) / 60)) ≤ 1 := by
  have hn1 : (1 : ℝ) ≤ n := by
    exact_mod_cast (paperSizeThreshold_one_lt hqr).le.trans hn
  have hn0 : (0 : ℝ) < n := zero_lt_one.trans_le hn1
  have hcoef : (8 * (H : ℝ)) ^ 2 ≤ (4 * q : ℝ) ^ (3 * q) := by
    exact_mod_cast exchange_eight_square_bound hqr hH
  have hg := paper_threshold_alpha_rpow_lower hqr hn (s := 3 * q)
    (t := (1 / 30 : ℝ)) (by norm_num) (by push_cast; linarith)
  have hsquare : (8 * (H : ℝ)) ^ 2 ≤
      ((n : ℝ) ^ (paperAlpha q (r + 1) / 60)) ^ 2 := by
    have heq : ((n : ℝ) ^ (paperAlpha q (r + 1) / 60)) ^ 2 =
        (n : ℝ) ^ (paperAlpha q (r + 1) * (1 / 30)) := by
      rw [← Real.rpow_mul_natCast hn0.le]
      congr 1
      norm_num
      ring
    rw [heq]
    exact hcoef.trans hg
  have hc := (sq_le_sq₀ (by positivity : 0 ≤ 8 * (H : ℝ))
    (Real.rpow_nonneg hn0.le _)).mp hsquare
  have hm := mul_le_mul_of_nonneg_right hc
    (Real.rpow_nonneg hn0.le (-(paperAlpha q (r + 1) / 60)))
  simpa only [← Real.rpow_add hn0, add_neg_cancel, Real.rpow_zero] using hm

theorem relaxed_colour_error_le_eighth_paper_threshold {q r n H : ℕ}
    (hqr : r + 1 < q) (hn : paperSizeThreshold q (r + 1) ≤ n) (hh : 1 ≤ H)
    (hH : H ≤ 3 * (2 * q) ^ (r + 1) * (q.choose (r + 1)) ^ 2) :
    (n : ℝ) ^ (-(paperAlpha q (r + 1) / 60)) ≤ 1 / 8 := by
  have hm := mul_le_mul_of_nonneg_right (by exact_mod_cast hh : (1 : ℝ) ≤ H)
    (Real.rpow_nonneg (Nat.cast_nonneg n) (-(paperAlpha q (r + 1) / 60)))
  have hs := relaxed_colour_error_small_paper_threshold hqr hn hH
  linarith only [hm, hs]

theorem relaxed_colour_joint_power_paper_threshold {q r n H : ℕ}
    (hqr : r + 1 < q) (hn : paperSizeThreshold q (r + 1) ≤ n) (hh : 1 ≤ H)
    (hH : H ≤ 3 * (2 * q) ^ (r + 1) * (q.choose (r + 1)) ^ 2)
    {p d t : ℝ} (hd : 0 ≤ d) (ht : 0 ≤ t)
    (hpd : (1 - (n : ℝ) ^ (-(paperAlpha q (r + 1) / 60))) * d ≤ p)
    (hpair : t ≤ (1 + (n : ℝ) ^ (-(paperAlpha q (r + 1) / 60))) * d ^ 2)
    (M : ℕ) (hMH : M ≤ H) : t ^ M ≤ 2 * p ^ (2 * M) :=
  joint_power_le_twice M H hMH hd ht (Real.rpow_nonneg (Nat.cast_nonneg n) _)
    (relaxed_colour_error_le_eighth_paper_threshold hqr hn hh hH)
    (relaxed_colour_error_small_paper_threshold hqr hn hH) hpd hpair

end Arxiv2411_18291
