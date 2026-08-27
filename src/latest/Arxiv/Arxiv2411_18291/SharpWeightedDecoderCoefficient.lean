import Arxiv.Arxiv2411_18291.WeightedDecoderNumerics

/-! # Keeping the factorial and binomial factors together in weighted decoding -/

namespace Arxiv2411_18291

theorem weightedDecoderCoefficient_three_q {q r : ℕ} (hqr : r + 1 < q) :
    weightedDecoderCoefficient q r ≤ (4 * q) ^ (3 * q) := by
  have hq : 2 ≤ q := by omega
  have hf : (r + 1).factorial ≤ q ^ q :=
    (Nat.factorial_le hqr.le).trans (Nat.factorial_le_pow q)
  have hJ := Nat.choose_le_two_pow (q + 1) (q - r)
  have hK : (q + (r + 1)).choose (r + 1) ≤ 2 ^ (2 * q) :=
    (Nat.choose_le_two_pow _ _).trans (Nat.pow_le_pow_right (by decide) (by omega))
  have hJpos : 1 ≤ (q + 1).choose (q - r) := Nat.choose_pos (by omega)
  have hKpos : 1 ≤ (q + (r + 1)).choose (r + 1) := Nat.choose_pos (by omega)
  have hinner : 1 ≤ (q + 1).choose (q - r) * (q + (r + 1)).choose (r + 1) *
      (8 * (r + 1).factorial) := Nat.succ_le_of_lt (by positivity)
  have hpow (a : ℕ) : a ^ (2 * q) = (a ^ q) ^ 2 := by
    rw [← pow_mul]
    congr 1
    omega
  have hfour : (4 : ℕ) ^ q = (2 ^ q) ^ 2 := by
    calc
      _ = (2 ^ 2) ^ q := by norm_num
      _ = 2 ^ (2 * q) := (pow_mul _ _ _).symm
      _ = _ := hpow 2
  have hbase : (4 * q) ^ (2 * q) = (2 ^ q) ^ 4 * (q ^ q) ^ 2 := by
    rw [mul_pow, hpow 4, hpow q, hfour]
    ring
  calc
    _ ≤ 2 * (2 ^ q * (r + 1).factorial) *
        ((q + 1).choose (q - r) * (q + (r + 1)).choose (r + 1) *
          (8 * (r + 1).factorial)) := by
      unfold weightedDecoderCoefficient
      nlinarith only [Nat.mul_le_mul_left (2 ^ q * (r + 1).factorial) hinner]
    _ ≤ 2 * (2 ^ q * (q ^ q)) *
        (2 ^ (q + 1) * 2 ^ (2 * q) * (8 * (q ^ q))) := by gcongr
    _ = 32 * (4 * q) ^ (2 * q) := by rw [pow_succ, hpow 2, hbase]; ring
    _ ≤ (4 * q) ^ 2 * (4 * q) ^ (2 * q) :=
      Nat.mul_le_mul_right _ (by nlinarith only [hq])
    _ = (4 * q) ^ (2 + 2 * q) := (pow_add _ _ _).symm
    _ ≤ _ := Nat.pow_le_pow_right (by omega) (by omega)

theorem weightedDecoderCoefficient_density_paper_threshold {q r n : ℕ}
    (hqr : r + 1 < q) (hn : paperSizeThreshold q (r + 1) ≤ n) :
    (weightedDecoderCoefficient q r : ℝ) *
        (n : ℝ) ^ (-(3 * paperAlpha q (r + 1) / 5)) ≤
      (n : ℝ) ^ (-(17 * paperAlpha q (r + 1) / 30)) := by
  have hn0 : (0 : ℝ) < n := by
    exact_mod_cast Nat.zero_lt_one.trans ((paperSizeThreshold_one_lt hqr).trans_le hn)
  have hc : (weightedDecoderCoefficient q r : ℝ) ≤ (4 * q : ℝ) ^ (3 * q) := by
    exact_mod_cast weightedDecoderCoefficient_three_q hqr
  have hg : (4 * q : ℝ) ^ (3 * q) ≤
      (n : ℝ) ^ (paperAlpha q (r + 1) / 30) := by
    have hh := paper_threshold_alpha_rpow_lower hqr hn (s := 3 * q)
      (t := (1 / 30 : ℝ)) (by norm_num) (by push_cast; linarith)
    simpa only [div_eq_mul_inv, one_mul] using hh
  calc
    _ ≤ (n : ℝ) ^ (paperAlpha q (r + 1) / 30) *
        (n : ℝ) ^ (-(3 * paperAlpha q (r + 1) / 5)) :=
      mul_le_mul_of_nonneg_right (hc.trans hg) (Real.rpow_nonneg hn0.le _)
    _ = _ := by rw [← Real.rpow_add hn0]; congr 1; ring

end Arxiv2411_18291
