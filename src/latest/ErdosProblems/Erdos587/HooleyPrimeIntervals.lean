import ErdosProblems.Erdos520.External.BrunTitchmarsh
import Mathlib

/-!
# A uniform short-prime-interval bound

The already proved Selberg-sieve estimate is specialized at the fourth
root of the lower endpoint. The resulting square-root error is uniform
even for a singleton interval. No prime number theorem is needed.
-/

open scoped BigOperators

namespace Erdos587

lemma one_add_cube_le_twenty_eight_exp {t : ℝ} (ht : 0 ≤ t) :
    (1 + t) ^ 3 ≤ 28 * Real.exp t := by
  have hpow := Real.pow_div_factorial_le_exp t ht 3
  have hadd := add_pow_le (show (0 : ℝ) ≤ 1 by norm_num) ht 3
  have hone : 1 ≤ Real.exp t := Real.one_le_exp_iff.mpr ht
  norm_num at hpow hadd
  nlinarith only [hpow, hadd, hone]

theorem primesBetween_le_log_main_sqrt_error {x h : ℝ}
    (hx : 1 < x) (hh : 0 ≤ h) :
    (BrunTitchmarsh.primesBetween x (x + h) : ℝ) ≤
      8 * h / Real.log x + 168 * Real.sqrt x := by
  have hxpos : 0 < x := lt_trans zero_lt_one hx
  obtain rfl | hh := hh.eq_or_lt
  · have hcard : BrunTitchmarsh.primesBetween x x ≤ 1 := by
      unfold BrunTitchmarsh.primesBetween
      apply (Finset.card_filter_le _ _).trans
      rw [Nat.card_Icc]
      have hfc : Nat.floor x ≤ Nat.ceil x := Nat.floor_le_ceil x
      omega
    have hcardR : (BrunTitchmarsh.primesBetween x x : ℝ) ≤ 1 := by exact_mod_cast hcard
    have hsqrt : 1 ≤ Real.sqrt x := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_le_sqrt hx.le
    simpa using hcardR.trans (show (1 : ℝ) ≤ 168 * Real.sqrt x by linarith)
  · let z := Real.exp (Real.log x / 4)
    have hlog : 0 < Real.log x := Real.log_pos hx
    have hz : 1 < z := Real.one_lt_exp_iff.mpr (by positivity)
    have hlogz : Real.log z = Real.log x / 4 := Real.log_exp _
    have hz4 : z ^ 4 = x := by
      rw [← Real.exp_nat_mul]
      norm_num
      rw [show (4 : ℝ) * (Real.log x / 4) = Real.log x by ring]
      exact Real.exp_log hxpos
    have hzsq : z ^ 2 = Real.sqrt x := by
      apply (sq_eq_sq₀ (sq_nonneg z) (Real.sqrt_nonneg x)).mp
      rw [← pow_mul, show (2 : ℕ) * 2 = 4 by norm_num, hz4, Real.sq_sqrt hxpos.le]
    have hcube : (1 + Real.log z) ^ 3 ≤ 28 * z := by
      simpa only [Real.exp_log (lt_trans zero_lt_one hz)] using
        one_add_cube_le_twenty_eight_exp (Real.log_nonneg hz.le)
    have hmain : 2 * h / Real.log z = 8 * h / Real.log x := by
      rw [hlogz]
      ring
    calc
      _ ≤ 2 * h / Real.log z + 6 * z * (1 + Real.log z) ^ 3 :=
        BrunTitchmarsh.primesBetween_le x h z hxpos hh hz
      _ ≤ 8 * h / Real.log x + 6 * z * (28 * z) := by
        rw [hmain]
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hcube (by positivity))
      _ = _ := by rw [show 6 * z * (28 * z) = 168 * z ^ 2 by ring, hzsq]

noncomputable def primeIntervalReciprocal (x y : ℝ) : ℝ :=
  ∑ p ∈ (Finset.Icc (Nat.ceil x) (Nat.floor y)).filter Nat.Prime, (1 : ℝ) / p

lemma primeIntervalReciprocal_le_card_div {x y : ℝ} (hx : 0 < x) :
    primeIntervalReciprocal x y ≤ (BrunTitchmarsh.primesBetween x y : ℝ) / x := by
  unfold primeIntervalReciprocal BrunTitchmarsh.primesBetween
  calc
    _ ≤ ∑ _p ∈ (Finset.Icc (Nat.ceil x) (Nat.floor y)).filter Nat.Prime, (1 : ℝ) / x := by
      apply Finset.sum_le_sum
      intro p hp
      have hxp : x ≤ (p : ℝ) := Nat.ceil_le.mp (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1
      exact one_div_le_one_div_of_le hx hxp
    _ = _ := by simp [div_eq_mul_inv]

/-- The estimate remains useful when the interval length is smaller than
the square root of its lower endpoint. -/
theorem primeIntervalReciprocal_le_log_main_sqrt_error {x h : ℝ}
    (hx : 1 < x) (hh : 0 ≤ h) :
    primeIntervalReciprocal x (x + h) ≤
      8 * h / (x * Real.log x) + 168 / Real.sqrt x := by
  have hxpos : 0 < x := lt_trans zero_lt_one hx
  have hsqrt : 0 < Real.sqrt x := Real.sqrt_pos.mpr hxpos
  calc
    _ ≤ (BrunTitchmarsh.primesBetween x (x + h) : ℝ) / x :=
      primeIntervalReciprocal_le_card_div hxpos
    _ ≤ (8 * h / Real.log x + 168 * Real.sqrt x) / x :=
      div_le_div_of_nonneg_right (primesBetween_le_log_main_sqrt_error hx hh) hxpos.le
    _ = _ := by
      have hsq := Real.sq_sqrt hxpos.le
      have hlog : Real.log x ≠ 0 := (Real.log_pos hx).ne'
      field_simp
      linear_combination 168 * Real.log x * hsq

end Erdos587
