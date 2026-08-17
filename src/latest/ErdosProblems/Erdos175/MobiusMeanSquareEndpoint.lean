/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ErdosProblems.Erdos175.MobiusMeanSquare

/-!
# The truncated Mobius mean-square endpoint

This file packages the positive least-common-multiple estimate proved in
`MobiusMeanSquare` as the concrete coefficient bound used by the Type II
argument.  The interval is the half-open dyadic interval `(N, 2N]`.
-/

namespace Erdos175

open scoped BigOperators
open ArithmeticFunction

/-- The real truncated Mobius divisor sum used by Granville--Ramare. -/
noncomputable def truncatedMobiusDivisorSum (z n : ℕ) : ℝ :=
  ∑ d ∈ (Finset.Icc 1 z).filter (fun d => d ∣ n),
    ((ArithmeticFunction.moebius d : ℤ) : ℝ)

/-- Pointwise expansion of the square as a least-common-multiple sum. -/
theorem truncatedMobiusDivisorSum_sq (z n : ℕ) :
    truncatedMobiusDivisorSum z n ^ 2 =
      ∑ a ∈ Finset.Icc 1 z, ∑ b ∈ Finset.Icc 1 z,
        if Nat.lcm a b ∣ n then
          ((ArithmeticFunction.moebius a : ℤ) : ℝ) *
            ((ArithmeticFunction.moebius b : ℤ) : ℝ)
        else 0 := by
  classical
  rw [truncatedMobiusDivisorSum, pow_two]
  rw [Finset.sum_filter]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  by_cases han : a ∣ n <;> by_cases hbn : b ∣ n
  · rw [if_pos han, if_pos hbn, if_pos (Nat.lcm_dvd han hbn)]
  · rw [if_pos han, if_neg hbn, mul_zero, if_neg]
    intro hl
    exact hbn (dvd_trans (Nat.dvd_lcm_right a b) hl)
  · rw [if_neg han, zero_mul, if_neg]
    intro hl
    exact han (dvd_trans (Nat.dvd_lcm_left a b) hl)
  · rw [if_neg han, zero_mul, if_neg]
    intro hl
    exact han (dvd_trans (Nat.dvd_lcm_left a b) hl)

/-- The number of multiples of a positive modulus in `(N,2N]` is at most
`2N/q`.  The rational upper bound avoids any rounding-error term. -/
theorem intervalMultipleCount_le_two_mul_div
    (N q : ℕ) :
    (intervalMultipleCount N q : ℝ) ≤ (2 * (N : ℝ)) / (q : ℝ) := by
  have hnat : intervalMultipleCount N q ≤ (2 * N) / q := by
    rw [intervalMultipleCount_eq]
    exact Nat.sub_le _ _
  calc
    (intervalMultipleCount N q : ℝ) ≤ (((2 * N) / q : ℕ) : ℝ) := by
      exact_mod_cast hnat
    _ ≤ ((2 * N : ℕ) : ℝ) / (q : ℝ) := Nat.cast_div_le
    _ = (2 * (N : ℝ)) / (q : ℝ) := by push_cast; ring

/-- Absolute value of the real Mobius value is its square. -/
theorem abs_mobius_real_eq_mobiusSqReal (n : ℕ) :
    |((ArithmeticFunction.moebius n : ℤ) : ℝ)| = mobiusSqReal n := by
  by_cases hn : Squarefree n
  · have h := ArithmeticFunction.abs_moebius_eq_one_of_squarefree hn
    have hreal : |((ArithmeticFunction.moebius n : ℤ) : ℝ)| = 1 := by
      exact_mod_cast h
    rw [hreal, mobiusSqReal_eq_one_of_squarefree hn]
  · rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hn,
      mobiusSqReal_eq_zero_of_not_squarefree hn]
    norm_num

/-- Summing the pointwise expansion counts multiples of each lcm. -/
theorem sum_truncatedMobiusDivisorSum_sq_eq_lcm (N z : ℕ) :
    (∑ n ∈ Finset.Ioc N (2 * N), truncatedMobiusDivisorSum z n ^ 2) =
      ∑ a ∈ Finset.Icc 1 z, ∑ b ∈ Finset.Icc 1 z,
        ((ArithmeticFunction.moebius a : ℤ) : ℝ) *
            ((ArithmeticFunction.moebius b : ℤ) : ℝ) *
          (intervalMultipleCount N (Nat.lcm a b) : ℝ) := by
  classical
  calc
    (∑ n ∈ Finset.Ioc N (2 * N), truncatedMobiusDivisorSum z n ^ 2) =
        ∑ n ∈ Finset.Ioc N (2 * N), ∑ a ∈ Finset.Icc 1 z,
          ∑ b ∈ Finset.Icc 1 z,
            if Nat.lcm a b ∣ n then
              ((ArithmeticFunction.moebius a : ℤ) : ℝ) *
                ((ArithmeticFunction.moebius b : ℤ) : ℝ)
            else 0 := by
      apply Finset.sum_congr rfl
      intro n hn
      exact truncatedMobiusDivisorSum_sq z n
    _ = ∑ a ∈ Finset.Icc 1 z, ∑ b ∈ Finset.Icc 1 z,
          ∑ n ∈ Finset.Ioc N (2 * N),
            if Nat.lcm a b ∣ n then
              ((ArithmeticFunction.moebius a : ℤ) : ℝ) *
                ((ArithmeticFunction.moebius b : ℤ) : ℝ)
            else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.sum_comm]
    _ = ∑ a ∈ Finset.Icc 1 z, ∑ b ∈ Finset.Icc 1 z,
        ((ArithmeticFunction.moebius a : ℤ) : ℝ) *
            ((ArithmeticFunction.moebius b : ℤ) : ℝ) *
          (intervalMultipleCount N (Nat.lcm a b) : ℝ) := by
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      rw [← Finset.sum_filter]
      simp only [intervalMultipleCount, Finset.sum_const, nsmul_eq_mul]
      ring

/-- A signed lcm-count term is dominated by the corresponding positive
Mobius-square term and the rational multiple-count bound. -/
theorem mobius_mul_intervalMultipleCount_le
    (N a b : ℕ) :
    ((ArithmeticFunction.moebius a : ℤ) : ℝ) *
          ((ArithmeticFunction.moebius b : ℤ) : ℝ) *
        (intervalMultipleCount N (Nat.lcm a b) : ℝ) ≤
      (2 * (N : ℝ)) *
        (mobiusSqReal a * mobiusSqReal b / (Nat.lcm a b : ℝ)) := by
  have hmu :
      ((ArithmeticFunction.moebius a : ℤ) : ℝ) *
          ((ArithmeticFunction.moebius b : ℤ) : ℝ) ≤
        mobiusSqReal a * mobiusSqReal b := by
    calc
      ((ArithmeticFunction.moebius a : ℤ) : ℝ) *
          ((ArithmeticFunction.moebius b : ℤ) : ℝ) ≤
          |((ArithmeticFunction.moebius a : ℤ) : ℝ) *
            ((ArithmeticFunction.moebius b : ℤ) : ℝ)| := le_abs_self _
      _ = mobiusSqReal a * mobiusSqReal b := by
        rw [abs_mul, abs_mobius_real_eq_mobiusSqReal,
          abs_mobius_real_eq_mobiusSqReal]
  have hcount := intervalMultipleCount_le_two_mul_div N (Nat.lcm a b)
  calc
    ((ArithmeticFunction.moebius a : ℤ) : ℝ) *
          ((ArithmeticFunction.moebius b : ℤ) : ℝ) *
        (intervalMultipleCount N (Nat.lcm a b) : ℝ) ≤
      (mobiusSqReal a * mobiusSqReal b) *
        (intervalMultipleCount N (Nat.lcm a b) : ℝ) := by
          gcongr
    _ ≤ (mobiusSqReal a * mobiusSqReal b) *
        ((2 * (N : ℝ)) / (Nat.lcm a b : ℝ)) := by
          exact mul_le_mul_of_nonneg_left hcount
            (mul_nonneg (mobiusSqReal_nonneg a) (mobiusSqReal_nonneg b))
    _ = (2 * (N : ℝ)) *
        (mobiusSqReal a * mobiusSqReal b / (Nat.lcm a b : ℝ)) := by ring

/-- Granville--Ramare Proposition 10.1 in the explicit weakened form needed
by the Type II estimate.  The proof actually gives the smaller coefficient
`16/27`; the published `8/9` form is exposed for downstream use. -/
theorem granville_ramare_prop_10_1
    (N z : ℕ) (hz : 1 ≤ z) :
    (∑ n ∈ Finset.Ioc N (2 * N), truncatedMobiusDivisorSum z n ^ 2) ≤
      (8 / 9 : ℝ) * (N : ℝ) * (Real.log z + 3) ^ 3 := by
  have hpos := sum_mobiusSqReal_lcm_le z hz
  have hlog : 0 ≤ Real.log z + 3 := by
    have : 0 ≤ Real.log (z : ℝ) := Real.log_nonneg (by exact_mod_cast hz)
    linarith
  calc
    (∑ n ∈ Finset.Ioc N (2 * N), truncatedMobiusDivisorSum z n ^ 2) =
        ∑ a ∈ Finset.Icc 1 z, ∑ b ∈ Finset.Icc 1 z,
          ((ArithmeticFunction.moebius a : ℤ) : ℝ) *
              ((ArithmeticFunction.moebius b : ℤ) : ℝ) *
            (intervalMultipleCount N (Nat.lcm a b) : ℝ) :=
      sum_truncatedMobiusDivisorSum_sq_eq_lcm N z
    _ ≤ ∑ a ∈ Finset.Icc 1 z, ∑ b ∈ Finset.Icc 1 z,
        (2 * (N : ℝ)) *
          (mobiusSqReal a * mobiusSqReal b / (Nat.lcm a b : ℝ)) := by
      apply Finset.sum_le_sum
      intro a ha
      apply Finset.sum_le_sum
      intro b hb
      exact mobius_mul_intervalMultipleCount_le N a b
    _ = (2 * (N : ℝ)) *
        ∑ a ∈ Finset.Icc 1 z, ∑ b ∈ Finset.Icc 1 z,
          mobiusSqReal a * mobiusSqReal b / (Nat.lcm a b : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.mul_sum]
    _ ≤ (2 * (N : ℝ)) *
        ((8 / 27 : ℝ) * (Real.log z + 3) ^ 3) := by
      exact mul_le_mul_of_nonneg_left hpos (by positivity)
    _ ≤ (8 / 9 : ℝ) * (N : ℝ) * (Real.log z + 3) ^ 3 := by
      have hN0 : (0 : ℝ) ≤ (N : ℝ) := by positivity
      have hprod : 0 ≤ (N : ℝ) * (Real.log z + 3) ^ 3 :=
        mul_nonneg hN0 (pow_nonneg hlog 3)
      nlinarith

end Erdos175
