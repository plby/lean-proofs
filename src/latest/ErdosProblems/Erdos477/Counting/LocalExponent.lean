/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
The square-root lower bound for the two-dimensional local determinant exponent.
Formal author: Codex.
-/

import ErdosProblems.Erdos477.Counting.LocalDeterminant

namespace Erdos477.Counting

/-- An explicit version of the leading `2√2/3 · s^(3/2)` local exponent,
with a linear error. No asymptotic or point-counting hypothesis is used. -/
theorem localExponent_lower_bound (s : ℕ) :
    (2 : ℝ) / 3 * s * Real.sqrt (2 * s) - 3 * s ≤
      (localExponent s (Nat.sqrt (2 * s)) : ℝ) := by
  let m := Nat.sqrt (2 * s)
  let K := m * (m + 1) * (m + 2) / 6
  have hn : m * s ≤ localExponent s m + K := by
    dsimp only [localExponent, K]
    omega
  have hk : 6 * K ≤ m * (m + 1) * (m + 2) := by
    dsimp only [K]
    omega
  have hnR : (m : ℝ) * s ≤ (localExponent s m : ℝ) + K := by exact_mod_cast hn
  have hkR : (6 : ℝ) * K ≤ (m : ℝ) * (m + 1) * (m + 2) := by exact_mod_cast hk
  have hm2 : (m : ℝ) ^ 2 ≤ 2 * s := by
    have h := Nat.sqrt_le (2 * s)
    change m * m ≤ 2 * s at h
    rw [pow_two]
    exact_mod_cast h
  have hm1 : (m : ℝ) ≤ 2 * s := by exact_mod_cast Nat.sqrt_le_self (2 * s)
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hs0 : (0 : ℝ) ≤ s := Nat.cast_nonneg _
  have hm3 : (m : ℝ) ^ 3 ≤ 2 * m * s := by
    have h := mul_le_mul_of_nonneg_left hm2 hm0
    nlinarith
  have hroot : Real.sqrt (2 * (s : ℝ)) ≤ (m : ℝ) + 1 := by
    have h := (Real.real_sqrt_lt_nat_sqrt_succ (a := 2 * s)).le
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using h
  have hrootmul : 2 * (s : ℝ) * Real.sqrt (2 * s) ≤ 2 * s * ((m : ℝ) + 1) :=
    mul_le_mul_of_nonneg_left hroot (by positivity)
  have hmain : (4 : ℝ) * m * s ≤ 6 * (localExponent s m : ℝ) + 6 * s + 2 * m := by
    nlinarith
  change (2 : ℝ) / 3 * s * Real.sqrt (2 * s) - 3 * s ≤ (localExponent s m : ℝ)
  nlinarith

#print axioms localExponent_lower_bound
-- 'Erdos477.Counting.localExponent_lower_bound' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

end Erdos477.Counting
