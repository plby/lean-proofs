import Arxiv.Arxiv2411_18291.FiniteTypicalHostNumerics

/-! # An explicit threshold for corrected high-probability typicality

Here `r` is the face rank, so the sampled graph has edge rank `r + 1`.
The bound also fits below the paper threshold through the full exchange size.
-/

namespace Arxiv2411_18291

def correctedTypicalityThreshold (r h : ℕ) : ℕ :=
  (max (4 + 2 * h * 2 ^ h) (48 * (r * h) + 24 * h + 37)) ^ 40

theorem correctedTypicalityThreshold_pos (r h : ℕ) :
    0 < correctedTypicalityThreshold r h := by
  unfold correctedTypicalityThreshold
  apply pow_pos
  have hh := le_max_right (4 + 2 * h * 2 ^ h) (48 * (r * h) + 24 * h + 37)
  omega

theorem corrected_typicality_growth {r h n : ℕ}
    (hn : correctedTypicalityThreshold r h ≤ n) :
    (4 + 2 * h * 2 ^ h : ℝ) ≤ (n : ℝ) ^ (1 / 40 : ℝ) ∧
      (48 * (r * h) + 24 * h + 36 : ℝ) < (n : ℝ) ^ (1 / 40 : ℝ) := by
  let M := max (4 + 2 * h * 2 ^ h) (48 * (r * h) + 24 * h + 37)
  have hM : (M : ℝ) ≤ (n : ℝ) ^ (1 / 40 : ℝ) := by
    have hh := Real.rpow_le_rpow (Nat.cast_nonneg (M ^ 40))
      (show ((M ^ 40 : ℕ) : ℝ) ≤ n by exact_mod_cast hn)
      (by norm_num : (0 : ℝ) ≤ 1 / 40)
    rw [Nat.cast_pow, ← Real.rpow_natCast_mul (Nat.cast_nonneg M)] at hh
    norm_num at hh
    exact hh
  constructor
  · have hh : (4 + 2 * h * 2 ^ h : ℝ) ≤ M := by exact_mod_cast le_max_left _ _
    exact hh.trans hM
  · have hh : (48 * (r * h) + 24 * h + 37 : ℝ) ≤ M := by
      exact_mod_cast le_max_right _ _
    linarith only [hh, hM]

theorem correctedTypicalityThreshold_le_paperThreshold {q r h : ℕ}
    (hqr : r + 1 < q) (hh : 1 ≤ h)
    (hH : h ≤ 3 * (2 * q) ^ (r + 1) * (q.choose (r + 1)) ^ 2) :
    correctedTypicalityThreshold r h ≤ paperSizeThreshold q (r + 1) := by
  let n := paperSizeThreshold q (r + 1)
  let M := max (4 + 2 * h * 2 ^ h) (48 * (r * h) + 24 * h + 37)
  have hC : 4 + 2 * h * 2 ^ h ≤ (4 * q) ^ (10 * (q + h)) := by
    have hc := reserve_normalization_constant_le (K := h) (by omega : 2 ≤ q)
    omega
  have hL : 48 * (r * h) + 24 * h + 37 ≤ (4 * q) ^ (10 * (q + h)) := by
    have hl := reserve_tail_constant_lt (by omega : 2 ≤ q) hh (by omega : r ≤ q)
    omega
  have hM : (M : ℝ) ≤ (n : ℝ) ^ (1 / 40 : ℝ) :=
    (show (M : ℝ) ≤ (4 * q : ℝ) ^ (10 * (q + h)) by
      exact_mod_cast max_le hC hL).trans (paper_host_configuration_growth hqr le_rfl hh hH)
  have hpow := pow_le_pow_left₀ (Nat.cast_nonneg M) hM 40
  rw [← Real.rpow_mul_natCast (Nat.cast_nonneg n)] at hpow
  norm_num at hpow
  exact_mod_cast hpow

theorem typical_tail_lt_stretched_exp_of_growth {r h n : ℕ} (hn : 1 ≤ n)
    (hlarge : (48 * (r * h) + 24 * h + 36 : ℝ) < (n : ℝ) ^ (1 / 40 : ℝ)) :
    2 * (h + 2 : ℝ) * (n : ℝ) ^ (r * h) *
        Real.exp (-((n : ℝ) ^ (1 / 4 : ℝ) / 12)) <
      Real.exp (-((n : ℝ) ^ (1 / 10 : ℝ))) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  let x : ℝ := (n : ℝ) ^ (1 / 40 : ℝ)
  have hx2 : 2 ≤ x := by
    nlinarith only [hlarge, (Nat.cast_nonneg r : (0 : ℝ) ≤ r),
      (Nat.cast_nonneg h : (0 : ℝ) ≤ h)]
  have hx1 : 1 ≤ x := by linarith only [hx2]
  have hx0 : 0 < x := by linarith only [hx2]
  have hln : Real.log (n : ℝ) ≤ 40 * x := by
    have hh := Real.log_le_rpow_div (Nat.cast_nonneg n) (by norm_num : (0 : ℝ) < 1 / 40)
    convert hh using 1
    dsimp only [x]
    ring
  have hlogC : Real.log (2 * (h + 2 : ℝ)) ≤ 2 * h + 3 := by
    have hh := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 2 * (h + 2))
    linarith only [hh]
  let A := 2 * (h + 2 : ℝ) * (n : ℝ) ^ (r * h)
  have hA : 0 < A := by dsimp only [A]; positivity
  have hLA : Real.log A ≤ (40 * (r * h) + 2 * h + 3 : ℝ) * x := by
    dsimp only [A]
    rw [Real.log_mul (by positivity) (pow_pos hn0 _).ne', Real.log_pow]
    have hh := mul_le_mul_of_nonneg_left hln (Nat.cast_nonneg (r * h))
    have hcx := mul_le_mul_of_nonneg_left hx1
      (by positivity : (0 : ℝ) ≤ 2 * h + 3)
    push_cast at hh ⊢
    nlinarith only [hh, hlogC, hcx]
  have hlog : Real.log A < x ^ 2 := by
    have hC : (40 * (r * h) + 2 * h + 3 : ℝ) < x := by
      nlinarith only [hlarge, (Nat.cast_nonneg r : (0 : ℝ) ≤ r),
        (Nat.cast_nonneg h : (0 : ℝ) ≤ h)]
    have hh := mul_lt_mul_of_pos_right hC hx0
    exact hLA.trans_lt (by nlinarith only [hh])
  have hx4 : x ^ 2 ≤ x ^ 4 := pow_le_pow_right₀ hx1 (by norm_num)
  have hx6 : 24 ≤ x ^ 6 := by
    have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hx2 6
    norm_num at hh
    linarith only [hh]
  have hx10 : 24 * x ^ 4 ≤ x ^ 10 := by
    have hh := mul_le_mul_of_nonneg_right hx6 (pow_nonneg hx0.le 4)
    calc
      _ ≤ x ^ 6 * x ^ 4 := hh
      _ = _ := by rw [← pow_add]
  have hquarter : (n : ℝ) ^ (1 / 4 : ℝ) = x ^ 10 := by
    dsimp only [x]
    rw [← Real.rpow_mul_natCast hn0.le]
    norm_num
  have htenth : (n : ℝ) ^ (1 / 10 : ℝ) = x ^ 4 := by
    dsimp only [x]
    rw [← Real.rpow_mul_natCast hn0.le]
    norm_num
  calc
    _ = Real.exp (Real.log A - (n : ℝ) ^ (1 / 4 : ℝ) / 12) := by
      rw [sub_eq_add_neg, Real.exp_add, Real.exp_log hA]
    _ < Real.exp (-((n : ℝ) ^ (1 / 10 : ℝ))) := by
      apply Real.exp_lt_exp.mpr
      rw [hquarter, htenth]
      nlinarith only [hlog, hx4, hx10]

theorem corrected_typicality_tail {r h n : ℕ}
    (hn : correctedTypicalityThreshold r h ≤ n) :
    2 * (h + 2 : ℝ) * (n : ℝ) ^ (r * h) *
        Real.exp (-((n : ℝ) ^ (1 / 4 : ℝ) / 12)) <
      Real.exp (-((n : ℝ) ^ (1 / 10 : ℝ))) :=
  typical_tail_lt_stretched_exp_of_growth
    ((correctedTypicalityThreshold_pos r h).trans_le hn) (corrected_typicality_growth hn).2

end Arxiv2411_18291
