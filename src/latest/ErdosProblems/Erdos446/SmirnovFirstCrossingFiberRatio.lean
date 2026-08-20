/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.SmirnovFirstCrossingWords

/-!
# Erdős Problem 446: comparison of finite first-crossing fibers

After fixing a first-crossing prefix, the labels after the crossing label
have one more available slot than the labels before it.  This file proves
the exact real inequality between the resulting two products.
-/

namespace Erdos446

open Real

/-- Both types of suffix letter gain at least the symmetric ratio coming
from the labels after the crossing label. -/
theorem firstCrossing_suffix_ratio_le
    {N w p : ℕ} (hwN : w + 2 < N) (hpN : p ≤ N) :
    Real.exp (2 * (w + 1 : ℝ)) ≤
      ((((N + w + 1 : ℕ) : ℝ) / ((N - w - 1 : ℕ) : ℝ)) ^ p) *
      ((((N + w : ℕ) : ℝ) / ((N - w - 2 : ℕ) : ℝ)) ^ (N - p)) := by
  let A : ℝ := ((N + w + 1 : ℕ) : ℝ) / ((N - w - 1 : ℕ) : ℝ)
  let B : ℝ := ((N + w : ℕ) : ℝ) / ((N - w - 2 : ℕ) : ℝ)
  have hw1N : w + 1 < N := by omega
  have hmain : Real.exp (2 * (w + 1 : ℝ)) ≤ A ^ N := by
    convert exp_two_mul_le_ratio_pow (N := N) (c := w + 1) hw1N using 1 <;>
      simp [A, Nat.cast_add, Nat.sub_sub] <;> ring
  have hdenA : (0 : ℝ) < (N - w - 1 : ℕ) := by
    exact_mod_cast (show 0 < N - w - 1 by omega)
  have hdenB : (0 : ℝ) < (N - w - 2 : ℕ) := by
    exact_mod_cast (show 0 < N - w - 2 by omega)
  have hAB : A ≤ B := by
    dsimp [A, B]
    rw [div_le_div_iff₀ hdenA hdenB]
    simp only [Nat.sub_sub]
    push_cast [Nat.cast_sub (by omega : w + 1 ≤ N),
      Nat.cast_sub (by omega : w + 2 ≤ N), Nat.cast_add, Nat.cast_one]
    nlinarith
  have hA0 : 0 ≤ A := by dsimp [A]; positivity
  have hpow : A ^ (N - p) ≤ B ^ (N - p) :=
    pow_le_pow_left₀ hA0 hAB _
  calc
    Real.exp (2 * (w + 1 : ℝ)) ≤ A ^ N := hmain
    _ = A ^ p * A ^ (N - p) := by
      rw [← pow_add]
      congr 1
      omega
    _ ≤ A ^ p * B ^ (N - p) :=
      mul_le_mul_of_nonneg_left hpow (pow_nonneg hA0 _)
    _ = _ := by rfl

/-- Product form of the suffix comparison.  It also includes the boundary
case `N=w+2`, when the lower alphabet for labels before the crossing is
empty. -/
theorem exp_mul_truncated_suffix_le_full_suffix
    {N w p : ℕ} (hwN : w + 2 ≤ N) (hpN : p ≤ N) :
    Real.exp (2 * (w + 1 : ℝ)) *
        ((N - w - 1 : ℕ) : ℝ) ^ p *
        ((N - w - 2 : ℕ) : ℝ) ^ (N - p) ≤
      ((N + w + 1 : ℕ) : ℝ) ^ p *
        ((N + w : ℕ) : ℝ) ^ (N - p) := by
  rcases eq_or_lt_of_le hwN with heq | hlt
  · have hN : N = w + 2 := heq.symm
    subst N
    by_cases hp : p = w + 2
    · subst p
      have hratio := exp_two_mul_le_ratio_pow
        (N := w + 2) (c := w + 1) (by omega)
      convert hratio using 1 <;>
        simp [Nat.cast_add, Nat.sub_sub, Nat.add_assoc, Nat.add_left_comm,
          Nat.add_comm]
    · have hq : 0 < w + 2 - p := by omega
      have hzero : ((w + 2 - w - 2 : ℕ) : ℝ) ^ (w + 2 - p) = 0 := by
        simp [Nat.sub_sub, hq.ne']
      rw [hzero]
      simp
      positivity
  · have hratio := firstCrossing_suffix_ratio_le hlt hpN
    have hdenA : (0 : ℝ) < (N - w - 1 : ℕ) := by
      exact_mod_cast (show 0 < N - w - 1 by omega)
    have hdenB : (0 : ℝ) < (N - w - 2 : ℕ) := by
      exact_mod_cast (show 0 < N - w - 2 by omega)
    have hmul := mul_le_mul_of_nonneg_right hratio
      (mul_nonneg (pow_nonneg hdenA.le p)
        (pow_nonneg hdenB.le (N - p)))
    calc
      Real.exp (2 * (w + 1 : ℝ)) *
          ((N - w - 1 : ℕ) : ℝ) ^ p *
          ((N - w - 2 : ℕ) : ℝ) ^ (N - p) =
          Real.exp (2 * (w + 1 : ℝ)) *
            (((N - w - 1 : ℕ) : ℝ) ^ p *
              ((N - w - 2 : ℕ) : ℝ) ^ (N - p)) := by ring
      _ ≤
          (((((N + w + 1 : ℕ) : ℝ) / ((N - w - 1 : ℕ) : ℝ)) ^ p) *
            ((((N + w : ℕ) : ℝ) / ((N - w - 2 : ℕ) : ℝ)) ^ (N - p))) *
            (((N - w - 1 : ℕ) : ℝ) ^ p *
              ((N - w - 2 : ℕ) : ℝ) ^ (N - p)) := hmul
      _ = ((N + w + 1 : ℕ) : ℝ) ^ p *
          ((N + w : ℕ) : ℝ) ^ (N - p) := by
        rw [div_pow, div_pow]
        field_simp [hdenA.ne', hdenB.ne']

end Erdos446
