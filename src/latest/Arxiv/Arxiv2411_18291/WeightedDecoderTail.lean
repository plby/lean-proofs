import Arxiv.Arxiv2411_18291.PaperAlphaGrowth

/-! # Weighted decoder tails at the paper's size threshold

A deviation factor `n^(alpha/10)` overcomes the polynomial union bound even
though one increment can have weight of order `theta*n`. The logarithmic
estimate retains the inverse-alpha factor and bounds it explicitly.
-/

namespace Arxiv2411_18291

theorem paperInverseAlpha_le_two_q_power {q r : ℕ} (hqr : r + 1 < q) :
    paperInverseAlpha q (r + 1) ≤ (4 * q) ^ (2 * q + 2) := by
  have hq : 2 ≤ q := by omega
  have hb : 1 ≤ 4 * q := by omega
  have hp : (2 * q) ^ (r + 1) ≤ (4 * q) ^ q :=
    (Nat.pow_le_pow_left (by omega) _).trans (Nat.pow_le_pow_right hb hqr.le)
  have hk := Nat.pow_le_pow_left (Nat.choose_le_two_pow q (r + 1)) 2
  have hpow : (2 ^ q) ^ 2 = 4 ^ q := by
    rw [← pow_mul, Nat.mul_comm q 2, pow_mul]
    norm_num
  rw [hpow] at hk
  have h36 : 36 ≤ (4 * q) ^ 2 := by nlinarith only [hq]
  have hfour : 4 ^ q ≤ (4 * q) ^ q := Nat.pow_le_pow_left (by omega) q
  have hsq : (6 * q.choose (r + 1)) ^ 2 ≤ (4 * q) ^ 2 * (4 * q) ^ q := by
    rw [mul_pow]
    exact Nat.mul_le_mul h36 (hk.trans hfour)
  calc
    _ ≤ (4 * q) ^ q * ((4 * q) ^ 2 * (4 * q) ^ q) := Nat.mul_le_mul hp hsq
    _ = _ := by rw [← pow_add, ← pow_add]; congr 1; omega

theorem weighted_decoder_tail_constant_lt {q r n : ℕ} (hqr : r + 1 < q)
    (hn : paperSizeThreshold q (r + 1) ≤ n) :
    (30 * (r + 1) * paperInverseAlpha q (r + 1) : ℝ) <
      (n : ℝ) ^ (paperAlpha q (r + 1) / 20) := by
  have hq : 2 ≤ q := by omega
  have hq2 := Nat.mul_le_mul_left q hq
  have h30 : 30 * (r + 1) ≤ (4 * q) ^ 2 := by nlinarith only [hqr, hq2]
  have hconstant : 30 * (r + 1) * paperInverseAlpha q (r + 1) ≤
      (4 * q) ^ (2 * q + 4) := by
    calc
      _ ≤ (4 * q) ^ 2 * (4 * q) ^ (2 * q + 2) :=
        Nat.mul_le_mul h30 (paperInverseAlpha_le_two_q_power hqr)
      _ = _ := by rw [← pow_add]; congr 1; omega
  have hgap : (4 * q) ^ (2 * q + 4) < (4 * q) ^ (4 * q + 1) :=
    Nat.pow_lt_pow_right (by omega) (by omega)
  have hlt : (30 * (r + 1) * paperInverseAlpha q (r + 1) : ℝ) <
      (4 * q : ℝ) ^ (4 * q + 1) := by exact_mod_cast hconstant.trans_lt hgap
  have hqR : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hg := paper_threshold_alpha_rpow_lower (s := 4 * q + 1) hqr hn
    (by norm_num : (0 : ℝ) ≤ 1 / 20) (by push_cast; linarith only [hqR])
  exact hlt.trans_le (by simpa only [div_eq_mul_inv, one_mul] using hg)

theorem weighted_decoder_polynomial_tail {q r n M : ℕ} (hqr : r + 1 < q)
    (hn : paperSizeThreshold q (r + 1) ≤ n) (hM : M ≤ n) :
    (M : ℝ) * n.choose r *
      Real.exp (-((2 / 3 : ℝ) * (n : ℝ) ^ (paperAlpha q (r + 1) / 10))) < 1 := by
  have hn1 : (1 : ℝ) ≤ n := by
    exact_mod_cast (paperSizeThreshold_one_lt hqr).le.trans hn
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hn1
  have hα := paperAlpha_pos hqr
  have hA : (0 : ℝ) < paperInverseAlpha q (r + 1) := by
    exact_mod_cast paperInverseAlpha_pos hqr
  let x : ℝ := (n : ℝ) ^ (paperAlpha q (r + 1) / 20)
  have hx : 0 < x := Real.rpow_pos_of_pos hn0 _
  have hlog : Real.log (n : ℝ) ≤ 20 * paperInverseAlpha q (r + 1) * x := by
    calc
      _ ≤ x / (paperAlpha q (r + 1) / 20) :=
        Real.log_le_rpow_div hn0.le (by positivity)
      _ = _ := by rw [paperAlpha_eq_inverse]; field_simp
  have hlogpow : Real.log ((n : ℝ) ^ (r + 1)) ≤
      20 * (r + 1) * paperInverseAlpha q (r + 1) * x := by
    rw [Real.log_pow]
    have hh := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg (r + 1))
    simpa only [Nat.cast_add, Nat.cast_one, mul_comm, mul_left_comm, mul_assoc] using hh
  have hscale := mul_lt_mul_of_pos_right (weighted_decoder_tail_constant_lt hqr hn) hx
  have hpow : (n : ℝ) ^ (paperAlpha q (r + 1) / 10) = x ^ 2 := by
    dsimp only [x]
    rw [← Real.rpow_mul_natCast hn0.le]
    congr 1
    ring
  have hexp : Real.log ((n : ℝ) ^ (r + 1)) -
      (2 / 3 : ℝ) * (n : ℝ) ^ (paperAlpha q (r + 1) / 10) < 0 := by
    rw [hpow]
    change (30 * (r + 1) * paperInverseAlpha q (r + 1) : ℝ) * x < x * x at hscale
    nlinarith only [hlogpow, hscale]
  have hpref : (M : ℝ) * n.choose r ≤ (n : ℝ) ^ (r + 1) := by
    calc
      _ ≤ (n : ℝ) * (n : ℝ) ^ r :=
        mul_le_mul (by exact_mod_cast hM) (by exact_mod_cast Nat.choose_le_pow n r)
          (Nat.cast_nonneg _) hn0.le
      _ = _ := by rw [pow_succ]; ring
  calc
    _ ≤ (n : ℝ) ^ (r + 1) *
        Real.exp (-((2 / 3 : ℝ) * (n : ℝ) ^ (paperAlpha q (r + 1) / 10))) :=
      mul_le_mul_of_nonneg_right hpref (Real.exp_pos _).le
    _ = Real.exp (Real.log ((n : ℝ) ^ (r + 1)) -
        (2 / 3 : ℝ) * (n : ℝ) ^ (paperAlpha q (r + 1) / 10)) := by
      rw [sub_eq_add_neg, Real.exp_add, Real.exp_log (pow_pos hn0 _)]
    _ < Real.exp 0 := Real.exp_lt_exp.mpr hexp
    _ = 1 := Real.exp_zero

theorem weighted_decoder_exponent_lower {r : ℕ} {θ n c : ℝ}
    (hθn : 1 ≤ θ * n) (hc : 1 ≤ c) :
    (2 / 3 : ℝ) * c ≤
      2 * (r + 1).factorial * (θ + θ) * n * c ^ 2 / ((2 + c) * (1 + θ * n)) := by
  have hθn0 : 0 ≤ θ * n := le_trans zero_le_one hθn
  have hc0 : 0 < c := lt_of_lt_of_le zero_lt_one hc
  have hden : 0 < (2 + c) * (1 + θ * n) := by positivity
  have hf : (1 : ℝ) ≤ (r + 1).factorial := by
    exact_mod_cast Nat.factorial_pos (r + 1)
  apply (le_div_iff₀ hden).mpr
  have hdenle : (2 + c) * (1 + θ * n) ≤ (3 * c) * (2 * (θ * n)) :=
    mul_le_mul (by linarith only [hc]) (by linarith only [hθn])
      (by positivity) (by positivity)
  have hh := mul_le_mul_of_nonneg_left hdenle (by positivity : (0 : ℝ) ≤ (2 / 3) * c)
  have hf' := mul_le_mul_of_nonneg_right hf
    (show 0 ≤ 4 * (θ * n) * c ^ 2 by positivity)
  nlinarith only [hh, hf']

end Arxiv2411_18291
