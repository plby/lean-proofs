import Arxiv.Arxiv2411_18291.PaperBoostParameters

/-! # The paper's explicit size parameter and its exact normalization -/

noncomputable section

namespace Arxiv2411_18291

def paperInverseAlpha (q r : ℕ) : ℕ := (2 * q) ^ r * (6 * q.choose r) ^ 2

def paperSizeThreshold (q r : ℕ) : ℕ := (4 * q) ^ (90 * q * paperInverseAlpha q r)

def paperRho (q r : ℕ) : ℝ := 1 / (6 * q.choose r : ℝ) ^ 2

def paperAlpha (q r : ℕ) : ℝ := paperRho q r / (2 * q : ℝ) ^ r

theorem paperInverseAlpha_pos {q r : ℕ} (hqr : r < q) : 0 < paperInverseAlpha q r := by
  have hq : 0 < q := by omega
  have hk : 0 < q.choose r := Nat.choose_pos hqr.le
  unfold paperInverseAlpha
  positivity

theorem paperAlpha_eq_inverse (q r : ℕ) :
    paperAlpha q r = (paperInverseAlpha q r : ℝ)⁻¹ := by
  unfold paperAlpha paperRho paperInverseAlpha
  push_cast
  simp only [div_eq_mul_inv, mul_inv_rev, one_mul]

theorem paperAlpha_mul_inverse {q r : ℕ} (hqr : r < q) :
    paperAlpha q r * (paperInverseAlpha q r : ℝ) = 1 := by
  rw [paperAlpha_eq_inverse]
  apply inv_mul_cancel₀
  exact_mod_cast (paperInverseAlpha_pos hqr).ne'

theorem paperAlpha_pos {q r : ℕ} (hqr : r < q) : 0 < paperAlpha q r := by
  rw [paperAlpha_eq_inverse]
  exact inv_pos.mpr (by exact_mod_cast paperInverseAlpha_pos hqr)

theorem paperRho_pos {q r : ℕ} (hqr : r < q) : 0 < paperRho q r := by
  have hk : (0 : ℝ) < q.choose r := by exact_mod_cast Nat.choose_pos hqr.le
  unfold paperRho
  positivity

theorem paperRho_le_one_div_36 {q r : ℕ} (hqr : r < q) : paperRho q r ≤ 1 / 36 := by
  have hk : (1 : ℝ) ≤ q.choose r := by exact_mod_cast Nat.choose_pos hqr.le
  unfold paperRho
  apply one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 36)
  nlinarith only [hk, sq_nonneg ((q.choose r : ℝ) - 1)]

theorem paperAlpha_le_rho {q r : ℕ} (hqr : r < q) : paperAlpha q r ≤ paperRho q r := by
  have hq : (1 : ℝ) ≤ 2 * q := by exact_mod_cast (show 1 ≤ 2 * q by omega)
  have hb : (1 : ℝ) ≤ (2 * q : ℝ) ^ r := one_le_pow₀ hq
  unfold paperAlpha
  apply (div_le_iff₀ (lt_of_lt_of_le zero_lt_one hb)).mpr
  exact le_mul_of_one_le_right (paperRho_pos hqr).le hb

theorem paperSizeThreshold_one_lt {q r : ℕ} (hqr : r < q) : 1 < paperSizeThreshold q r := by
  have hq : 0 < q := by omega
  have hA := paperInverseAlpha_pos hqr
  unfold paperSizeThreshold
  exact one_lt_pow₀ (by omega : 1 < 4 * q) (by positivity)

theorem paperSizeThreshold_rpow_alpha {q r : ℕ} (hqr : r < q) :
    (paperSizeThreshold q r : ℝ) ^ paperAlpha q r = (4 * q : ℝ) ^ (90 * q : ℝ) := by
  rw [paperSizeThreshold, Nat.cast_pow, ← Real.rpow_natCast_mul (by positivity)]
  push_cast
  congr 1
  calc
    _ = (90 * q : ℝ) * (paperAlpha q r * paperInverseAlpha q r) := by ring
    _ = _ := by rw [paperAlpha_mul_inverse hqr, mul_one]

end Arxiv2411_18291
