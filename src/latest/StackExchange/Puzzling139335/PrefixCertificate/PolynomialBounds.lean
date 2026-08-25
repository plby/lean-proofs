import Mathlib

/-!
# Polynomial estimates for the prefix certificate

All estimates are rational inequalities.  The two final positivity lemmas are
the algebraic part of the prefix support contradiction.
-/

namespace Puzzling139335.PrefixCertificate

def F0 (x : ℝ) : ℝ := x * (1 - x) * (1 - 9 * x - 3 * x ^ 2 + 3 * x ^ 3)

def A1 (x : ℝ) : ℝ := 3 * x ^ 3 - 2 * x ^ 2 + x + 4

def B1 (x : ℝ) : ℝ := 4 * x ^ 3 + 6 * x ^ 2 - 4 * x + 2

def A2 (x : ℝ) : ℝ := 3 * x ^ 3 - 4 * x ^ 2 + x + 4

def B2 (x : ℝ) : ℝ := 2 * x ^ 3 + 6 * x ^ 2 - 6 * x + 2

def Q (x : ℝ) : ℝ := x ^ 4 - 8 * x ^ 3 - 14 * x ^ 2 - 8 * x + 1

theorem F0_pos {x : ℝ} (hx0 : 0 < x) (hx : x < 3 / 28) : 0 < F0 x := by
  have hx2 : x ^ 2 < (9 / 784 : ℝ) := by
    nlinarith [mul_self_lt_mul_self hx0.le hx]
  have hbase : (1 / 784 : ℝ) < 1 - 9 * x - 3 * x ^ 2 := by
    linarith
  have hx3 : 0 ≤ x ^ 3 := by positivity
  unfold F0
  apply mul_pos
  · exact mul_pos hx0 (by linarith)
  · linarith

private theorem small_powers {x : ℝ} (hx0 : 0 < x) (hx : x < 3 / 28) :
    x ^ 2 < (1 / 64 : ℝ) ∧ x ^ 3 ≤ x ^ 2 := by
  have hx8 : x < (1 / 8 : ℝ) := by linarith
  constructor
  · nlinarith [mul_self_lt_mul_self hx0.le hx8]
  · have hx1 : x ≤ 1 := by linarith
    nlinarith [mul_nonneg (sub_nonneg.mpr hx1) (sq_nonneg x)]

theorem A1_bounds {x : ℝ} (hx0 : 0 < x) (hx : x < 3 / 28) :
    0 < A1 x ∧ A1 x < 9 / 2 := by
  obtain ⟨hx2, hx3⟩ := small_powers hx0 hx
  have hcube : 0 ≤ x ^ 3 := by positivity
  unfold A1
  constructor <;> nlinarith

theorem A2_bounds {x : ℝ} (hx0 : 0 < x) (hx : x < 3 / 28) :
    0 < A2 x ∧ A2 x < 9 / 2 := by
  obtain ⟨hx2, hx3⟩ := small_powers hx0 hx
  have hcube : 0 ≤ x ^ 3 := by positivity
  unfold A2
  constructor <;> nlinarith [sq_nonneg x]

theorem B1_lower {x : ℝ} (hx0 : 0 < x) (hx : x < 3 / 28) : 11 / 7 < B1 x := by
  have hcube : 0 ≤ x ^ 3 := by positivity
  unfold B1
  nlinarith [sq_nonneg x]

theorem B2_lower {x : ℝ} (hx0 : 0 < x) (hx : x < 3 / 28) : 19 / 14 < B2 x := by
  have hcube : 0 ≤ x ^ 3 := by positivity
  unfold B2
  nlinarith [sq_nonneg x]

private theorem mul_sum_lt {a x y : ℝ} (ha0 : 0 < a) (ha : a < 9 / 2)
    (hsum : x + y < 2 / 7) : a * (x + y) < 9 / 7 := by
  calc
    a * (x + y) < a * (2 / 7) := mul_lt_mul_of_pos_left hsum ha0
    _ < (9 / 2) * (2 / 7) := mul_lt_mul_of_pos_right ha (by norm_num)
    _ = 9 / 7 := by norm_num

theorem numerator_one_pos {x y : ℝ} (hx0 : 0 < x) (hx : x < 3 / 28)
    (hxy : x ≤ y) (hsum : x + y < 2 / 7) :
    0 < F0 x + (y - x) * (B1 x - A1 x * (x + y)) := by
  obtain ⟨ha0, ha⟩ := A1_bounds hx0 hx
  have hprod := mul_sum_lt ha0 ha hsum
  have hb := B1_lower hx0 hx
  exact add_pos_of_pos_of_nonneg (F0_pos hx0 hx)
    (mul_nonneg (sub_nonneg.mpr hxy) (by linarith))

theorem numerator_two_pos {x y : ℝ} (hx0 : 0 < x) (hx : x < 3 / 28)
    (hxy : x ≤ y) (hsum : x + y < 2 / 7) :
    0 < F0 x + (y - x) * (B2 x - A2 x * (x + y)) := by
  obtain ⟨ha0, ha⟩ := A2_bounds hx0 hx
  have hprod := mul_sum_lt ha0 ha hsum
  have hb := B2_lower hx0 hx
  exact add_pos_of_pos_of_nonneg (F0_pos hx0 hx)
    (mul_nonneg (sub_nonneg.mpr hxy) (by linarith))

theorem lt_three_twenty_eighths_of_Q_nonneg {x : ℝ} (hx0 : 0 < x)
    (hx1 : x < 1) (hQ : 0 ≤ Q x) : x < 3 / 28 := by
  have hcube : 0 < x ^ 3 := pow_pos hx0 3
  have hfour : x ^ 4 < x ^ 3 := by
    nlinarith [mul_lt_mul_of_pos_right hx1 hcube]
  by_contra h
  have hx : (3 / 28 : ℝ) ≤ x := le_of_not_gt h
  have hx2 : (9 / 784 : ℝ) ≤ x ^ 2 := by
    nlinarith [mul_self_le_mul_self (by norm_num : (0 : ℝ) ≤ 3 / 28) hx]
  unfold Q at hQ
  nlinarith

theorem sin_certificate_Q_identity (x : ℝ) :
    1 - 5 * (2 * x / (1 + x ^ 2)) + 4 * (2 * x / (1 + x ^ 2)) ^ 3 =
      (1 - x) ^ 2 * Q x / (1 + x ^ 2) ^ 3 := by
  have hd : 1 + x ^ 2 ≠ 0 := by positivity
  unfold Q
  field_simp
  ring

theorem sin_certificate_Q_nonneg {x : ℝ} (hx1 : x < 1) (_hx0 : 0 < x)
    (hs : 5 * (2 * x / (1 + x ^ 2)) - 4 * (2 * x / (1 + x ^ 2)) ^ 3 ≤ 1) :
    0 ≤ Q x := by
  have hd : 0 < (1 + x ^ 2) ^ 3 := by positivity
  have hf : 0 < (1 - x) ^ 2 := sq_pos_of_pos (sub_pos.mpr hx1)
  have hh : 0 ≤ 1 - 5 * (2 * x / (1 + x ^ 2)) +
      4 * (2 * x / (1 + x ^ 2)) ^ 3 := by linarith
  rw [sin_certificate_Q_identity] at hh
  have hp : 0 ≤ (1 - x) ^ 2 * Q x := by
    simpa using (le_div_iff₀ hd).mp hh
  exact (mul_nonneg_iff_of_pos_left hf).mp hp

end Puzzling139335.PrefixCertificate
