import Mathlib

/-! Dyadic scales with polynomial logarithmic overhead. -/

open Filter

namespace Erdos587

theorem eventually_nat_polynomial_le_two_pow (a d : ℕ) :
    ∀ᶠ t : ℕ in atTop, a * t ^ d ≤ 2 ^ t := by
  have hh := (isLittleO_pow_const_const_pow_of_one_lt (R := ℝ) d
    (r := 2) (by norm_num)).const_mul_left (a : ℝ)
  filter_upwards [hh.bound (show (0 : ℝ) < 1 by norm_num)] with t ht
  have ht' : (a : ℝ) * (t : ℝ) ^ d ≤ (2 : ℝ) ^ t := by
    simpa only [Real.norm_eq_abs,
      abs_of_nonneg (show 0 ≤ (a : ℝ) * (t : ℝ) ^ d by positivity),
      abs_of_nonneg (show 0 ≤ (2 : ℝ) ^ t by positivity), one_mul] using ht
  exact_mod_cast ht'

theorem dyadic_round_up_bounds {m : ℕ} (hm : 0 < m) :
    m ≤ 2 ^ (Nat.log 2 m + 1) ∧ 2 ^ (Nat.log 2 m + 1) ≤ 2 * m := by
  refine ⟨(Nat.lt_pow_succ_log_self (by norm_num) m).le, ?_⟩
  rw [pow_succ]
  have := Nat.pow_log_le_self 2 (by omega : m ≠ 0)
  omega

theorem dyadic_extra_upper (e₀ d t : ℕ) (ht : 0 < t) :
    2 ^ (e₀ + d * (Nat.log 2 (12 * t + 1) + 1)) ≤ (2 ^ e₀ * 26 ^ d) * t ^ d := by
  have hround := (dyadic_round_up_bounds (m := 12 * t + 1) (by omega)).2
  have hround' : 2 ^ (Nat.log 2 (12 * t + 1) + 1) ≤ 26 * t := by omega
  calc
    _ = 2 ^ e₀ * (2 ^ (Nat.log 2 (12 * t + 1) + 1)) ^ d := by
      rw [pow_add, ← pow_mul, Nat.mul_comm d]
    _ ≤ 2 ^ e₀ * (26 * t) ^ d := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hround' d)
    _ = (2 ^ e₀ * 26 ^ d) * t ^ d := by ring

theorem eventually_dyadic_extra_le (e₀ d : ℕ) :
    ∀ᶠ t : ℕ in atTop, e₀ + d * (Nat.log 2 (12 * t + 1) + 1) ≤ t := by
  filter_upwards [eventually_nat_polynomial_le_two_pow (2 ^ e₀ * 26 ^ d) d,
    eventually_ge_atTop 1] with t hpoly ht
  have hh := (dyadic_extra_upper e₀ d t ht).trans hpoly
  exact (Nat.pow_le_pow_iff_right (by omega : 1 < 2)).mp hh

theorem eventually_dyadic_initial_budget :
    ∀ᶠ t : ℕ in atTop, 4 * (12 * t + 1) ≤ 2 ^ t := by
  filter_upwards [eventually_nat_polynomial_le_two_pow 52 1,
    eventually_ge_atTop 1] with t hpoly ht
  simp only [pow_one] at hpoly
  omega

theorem log_subset_budget_le_dyadic {S H L : ℕ}
    (hS : 0 < S) (hH : 0 < H) (hSup : S ≤ 2 ^ L) (hHup : H ≤ 2 ^ L) :
    1 + Real.log ((S * H * 2 ^ L : ℕ) : ℝ) ≤ 4 * ((L : ℝ) + 1) := by
  have hM : S * H * 2 ^ L ≤ (2 ^ L) ^ 3 := by nlinarith [Nat.mul_le_mul hSup hHup]
  have hlog := Real.log_le_log (show (0 : ℝ) < ((S * H * 2 ^ L : ℕ) : ℝ) by positivity)
    (show ((S * H * 2 ^ L : ℕ) : ℝ) ≤ ((2 : ℝ) ^ L) ^ 3 by exact_mod_cast hM)
  rw [Real.log_pow, Real.log_pow] at hlog
  have hlogtwo : Real.log (2 : ℝ) ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    norm_num at hh
    exact hh
  have hL : (0 : ℝ) ≤ L := Nat.cast_nonneg _
  norm_num only [Nat.cast_ofNat] at hlog
  nlinarith

end Erdos587
