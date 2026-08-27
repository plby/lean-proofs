import Arxiv.Arxiv2411_18291.PaperSizeParameters

/-! # Explicit growth at the reserve density exponent -/

namespace Arxiv2411_18291

theorem paperRho_mul_inverseAlpha {q r : ℕ} (hqr : r < q) :
    paperRho q r * (paperInverseAlpha q r : ℝ) = (2 * q : ℝ) ^ r := by
  have hk : (q.choose r : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hqr.le).ne'
  unfold paperRho paperInverseAlpha
  push_cast
  field_simp

theorem paperSizeThreshold_rpow_rho {q r : ℕ} (hqr : r < q) :
    (paperSizeThreshold q r : ℝ) ^ paperRho q r =
      (4 * q : ℝ) ^ (90 * q * (2 * q) ^ r) := by
  rw [paperSizeThreshold, Nat.cast_pow, ← Real.rpow_natCast_mul (by positivity),
    ← Real.rpow_natCast]
  push_cast
  congr 1
  calc
    _ = (90 * q : ℝ) * (paperRho q r * paperInverseAlpha q r) := by ring
    _ = _ := by rw [paperRho_mul_inverseAlpha hqr]

/-- The paper's threshold makes the reciprocal reserve density larger than
all fixed exponential losses needed below. Here `r` is the graph rank. -/
theorem paper_threshold_reserve_growth {q r n : ℕ} (hqr : r < q)
    (hn : paperSizeThreshold q r ≤ n) :
    (4 * q : ℝ) ^ (10 * (q + q.choose r)) ≤ (n : ℝ) ^ paperRho q r := by
  have hq : 1 ≤ q := by omega
  have hD : 1 ≤ (2 * q) ^ r := one_le_pow₀ (by omega)
  have hK : q.choose r ≤ (2 * q) ^ r :=
    (Nat.choose_le_pow q r).trans (Nat.pow_le_pow_left (by omega) r)
  have hqD : q ≤ q * (2 * q) ^ r := by simpa using Nat.mul_le_mul_left q hD
  have hKD : q.choose r ≤ q * (2 * q) ^ r :=
    hK.trans (by simpa using Nat.mul_le_mul_right ((2 * q) ^ r) hq)
  have hexp : 10 * (q + q.choose r) ≤ 90 * q * (2 * q) ^ r := by
    nlinarith only [hqD, hKD]
  calc
    _ ≤ (4 * q : ℝ) ^ (90 * q * (2 * q) ^ r) :=
      pow_le_pow_right₀ (by exact_mod_cast (show 1 ≤ 4 * q by omega)) hexp
    _ = (paperSizeThreshold q r : ℝ) ^ paperRho q r :=
      (paperSizeThreshold_rpow_rho hqr).symm
    _ ≤ _ := Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hn)
      (paperRho_pos hqr).le

theorem paper_threshold_reserve_growth_le_rpow {q r n : ℕ} (hqr : r < q)
    (hn : paperSizeThreshold q r ≤ n) {t : ℝ} (ht : paperRho q r ≤ t) :
    (4 * q : ℝ) ^ (10 * (q + q.choose r)) ≤ (n : ℝ) ^ t := by
  have hn1 : (1 : ℝ) ≤ n := by
    exact_mod_cast (paperSizeThreshold_one_lt hqr).le.trans hn
  exact (paper_threshold_reserve_growth hqr hn).trans
    (Real.rpow_le_rpow_of_exponent_le hn1 ht)

theorem paperRho_mul_choose_le {q r : ℕ} (hqr : r < q) :
    paperRho q r * q.choose r ≤ 1 / 36 := by
  have hk : (1 : ℝ) ≤ q.choose r := by exact_mod_cast Nat.choose_pos hqr.le
  have hkpos : (0 : ℝ) < q.choose r := by linarith
  unfold paperRho
  rw [div_mul_eq_mul_div, one_mul]
  apply (div_le_iff₀ (by positivity)).mpr
  have hsq := mul_le_mul_of_nonneg_right hk hkpos.le
  nlinarith only [hsq]

end Arxiv2411_18291
