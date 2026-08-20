/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.CappedCompositions

/-!
# Erdős Problem 446: factorial suppression of Ford's crowding factor

Ford's exceptional-layer estimate contains

`(20 * m + 10) ^ (2 ^ m) / (2 ^ m - 2)!`.

This file gives a completely explicit uniform double-exponential upper
bound for that expression.  The constant is intentionally generous; what
matters in the subsequent dyadic summation is the factor
`2 ^ (-(2 ^ m))`.
-/

namespace Erdos446

/-- An elementary exponential lower bound used to start the factorial-block
recurrence. -/
theorem forty_mul_add_le_two_pow {m : ℕ} (hm : 10 ≤ m) :
    40 * m + 121 ≤ 2 ^ m := by
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ m hm ih =>
      rw [pow_succ]
      omega

/-- From depth ten onward, the increase in the crowding base is absorbed by
the first factor in the next factorial block. -/
theorem crowdingBase_square_le {m : ℕ} (hm : 10 ≤ m) :
    (40 * (m + 1) + 20) ^ 2 ≤
      (40 * m + 20) * (2 ^ m - 1) := by
  have hpow := forty_mul_add_le_two_pow hm
  have hlinear : 40 * m + 120 ≤ 2 ^ m - 1 := by omega
  nlinarith

/-- One step of the factorial-block comparison, stated integrally to avoid
any loss from division. -/
theorem crowdingFactorialBlock_step {m : ℕ} (hm : 10 ≤ m) :
    (40 * (m + 1) + 20) ^ (2 ^ (m + 1)) * (2 ^ m - 2).factorial ≤
      (40 * m + 20) ^ (2 ^ m) * (2 ^ (m + 1) - 2).factorial := by
  let n := 2 ^ m
  have hn : 2 ≤ n := by
    dsimp [n]
    have : 2 ^ 10 ≤ 2 ^ m := Nat.pow_le_pow_right (by omega) hm
    exact (by norm_num : 2 ≤ 2 ^ 10).trans this
  have hbase : (40 * (m + 1) + 20) ^ 2 ≤
      (40 * m + 20) * (n - 1) := by
    simpa [n] using crowdingBase_square_le hm
  have hpowBase := Nat.pow_le_pow_left hbase n
  have hfac0 := @Nat.factorial_mul_pow_le_factorial (n - 2) n
  have hfac : (n - 1) ^ n * (n - 2).factorial ≤
      (2 * n - 2).factorial := by
    have hfac' : (n - 2).factorial * (n - 1) ^ n ≤
        (2 * n - 2).factorial := by
      simpa [show n - 2 + 1 = n - 1 by omega,
        show n - 2 + n = 2 * n - 2 by omega] using hfac0
    simpa [Nat.mul_comm] using hfac'
  have hdouble : 2 ^ (m + 1) = 2 * n := by
    dsimp [n]
    rw [pow_succ]
    omega
  have hlargePow :
      (40 * (m + 1) + 20) ^ (2 ^ (m + 1)) =
        ((40 * (m + 1) + 20) ^ 2) ^ n := by
    rw [hdouble, pow_mul]
  calc
    (40 * (m + 1) + 20) ^ (2 ^ (m + 1)) * (2 ^ m - 2).factorial =
        ((40 * (m + 1) + 20) ^ 2) ^ n * (n - 2).factorial := by
      rw [hlargePow]
    _ ≤ ((40 * m + 20) * (n - 1)) ^ n * (n - 2).factorial :=
      Nat.mul_le_mul_right _ hpowBase
    _ = (40 * m + 20) ^ n *
        ((n - 1) ^ n * (n - 2).factorial) := by
      rw [mul_pow]
      ac_rfl
    _ ≤ (40 * m + 20) ^ n * (2 * n - 2).factorial :=
      Nat.mul_le_mul_left _ hfac
    _ = (40 * m + 20) ^ (2 ^ m) *
        (2 ^ (m + 1) - 2).factorial := by
      rw [hdouble]

/-- The normalized crowding term, with the desired `2^(2^m)` already
moved into its numerator. -/
noncomputable def fordCrowdingNormalizedTerm (m : ℕ) : ℝ :=
  ((40 * m + 20 : ℕ) : ℝ) ^ (2 ^ m) /
    (((2 ^ m - 2).factorial : ℕ) : ℝ)

/-- The normalized term decreases from depth ten onward. -/
theorem fordCrowdingNormalizedTerm_anti_step {m : ℕ} (hm : 10 ≤ m) :
    fordCrowdingNormalizedTerm (m + 1) ≤ fordCrowdingNormalizedTerm m := by
  have hstep := crowdingFactorialBlock_step hm
  have hstepR :
      (((40 * (m + 1) + 20 : ℕ) : ℝ) ^ (2 ^ (m + 1))) *
          (((2 ^ m - 2).factorial : ℕ) : ℝ) ≤
        (((40 * m + 20 : ℕ) : ℝ) ^ (2 ^ m)) *
          (((2 ^ (m + 1) - 2).factorial : ℕ) : ℝ) := by
    exact_mod_cast hstep
  dsimp [fordCrowdingNormalizedTerm]
  exact (div_le_div_iff₀ (by positivity :
      (0 : ℝ) < (((2 ^ (m + 1) - 2).factorial : ℕ) : ℝ))
    (by positivity :
      (0 : ℝ) < (((2 ^ m - 2).factorial : ℕ) : ℝ))).2 hstepR

/-- Explicit constant used in the suppression theorem. -/
noncomputable def fordCrowdingSuppressionConstant : ℝ :=
  (420 : ℝ) ^ 1024

theorem fordCrowdingSuppressionConstant_pos :
    0 < fordCrowdingSuppressionConstant := by
  dsimp [fordCrowdingSuppressionConstant]
  positivity

/-- Iterating the one-step comparison bounds every later normalized term by
the term at depth ten. -/
theorem fordCrowdingNormalizedTerm_le_ten {m : ℕ} (hm : 10 ≤ m) :
    fordCrowdingNormalizedTerm m ≤ fordCrowdingNormalizedTerm 10 := by
  induction m, hm using Nat.le_induction with
  | base => exact le_rfl
  | succ m hm ih =>
      exact (fordCrowdingNormalizedTerm_anti_step hm).trans ih

/-- The normalized crowding term is bounded by the explicit constant at
every depth. -/
theorem fordCrowdingNormalizedTerm_le (m : ℕ) :
    fordCrowdingNormalizedTerm m ≤ fordCrowdingSuppressionConstant := by
  by_cases hm : m ≤ 10
  · have hbase : 40 * m + 20 ≤ 420 := by omega
    have hexp : 2 ^ m ≤ 1024 := by
      exact Nat.pow_le_pow_right (by omega) hm
    have hpowBase :
        (((40 * m + 20 : ℕ) : ℝ) ^ (2 ^ m)) ≤
          (420 : ℝ) ^ (2 ^ m) := by
      exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast hbase) _
    have hpowExp : (420 : ℝ) ^ (2 ^ m) ≤ (420 : ℝ) ^ 1024 :=
      pow_le_pow_right₀ (by norm_num) hexp
    have hfac : (1 : ℝ) ≤
        (((2 ^ m - 2).factorial : ℕ) : ℝ) := by
      exact_mod_cast (Nat.factorial_pos (2 ^ m - 2))
    calc
      fordCrowdingNormalizedTerm m ≤
          (((40 * m + 20 : ℕ) : ℝ) ^ (2 ^ m)) := by
        dsimp [fordCrowdingNormalizedTerm]
        exact div_le_self (by positivity) hfac
      _ ≤ (420 : ℝ) ^ (2 ^ m) := hpowBase
      _ ≤ fordCrowdingSuppressionConstant := by
        exact hpowExp
  · have h10 : 10 ≤ m := by omega
    apply (fordCrowdingNormalizedTerm_le_ten h10).trans
    have hfac : (1 : ℝ) ≤ ((((1022 : ℕ).factorial : ℕ)) : ℝ) := by
      exact_mod_cast (Nat.factorial_pos 1022)
    change (420 : ℝ) ^ 1024 / ((((1022 : ℕ).factorial : ℕ)) : ℝ) ≤
      (420 : ℝ) ^ 1024
    exact div_le_self (by positivity) hfac

/-- Ford's factorial suppression between (32h) and (33).  The bound is
uniform in `m` and has the required double-exponential denominator. -/
theorem fordCrowdingFactorialSuppression (m : ℕ) :
    (((20 * m + 10 : ℕ) : ℝ) ^ (2 ^ m)) /
        (((2 ^ m - 2).factorial : ℕ) : ℝ) ≤
      fordCrowdingSuppressionConstant / (2 : ℝ) ^ (2 ^ m) := by
  have h := fordCrowdingNormalizedTerm_le m
  have hpow : (0 : ℝ) < (2 : ℝ) ^ (2 ^ m) := by positivity
  apply (le_div_iff₀ hpow).2
  calc
    (((20 * m + 10 : ℕ) : ℝ) ^ (2 ^ m) /
          (((2 ^ m - 2).factorial : ℕ) : ℝ)) *
        (2 : ℝ) ^ (2 ^ m) = fordCrowdingNormalizedTerm m := by
      dsimp [fordCrowdingNormalizedTerm]
      rw [div_mul_eq_mul_div, ← mul_pow]
      congr 2
      push_cast
      ring
    _ ≤ fordCrowdingSuppressionConstant := h

/-! ## The exponent-shifted form used in Ford's exceptional cover

The crowding witness at depth `h` produces an auxiliary index `m ≥ h - 3`.
Consequently (33) needs `2^(-2^(m+3))`, rather than merely
`2^(-2^m)`.  The same factorial-block argument works after normalizing by
`256^(2^m)`; only the finite starting point and explicit constant change.
-/

/-- A linear lower bound for `2^m` adequate for the base-256 recurrence. -/
theorem fiveThousandOneHundredTwenty_mul_add_le_two_pow
    {m : ℕ} (hm : 20 ≤ m) :
    5120 * m + 15361 ≤ 2 ^ m := by
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ m hm ih =>
      rw [pow_succ]
      omega

/-- After depth twenty, one new factorial block absorbs the squared increase
of the base normalized by `256`. -/
theorem strongCrowdingBase_square_le {m : ℕ} (hm : 20 ≤ m) :
    (5120 * (m + 1) + 2560) ^ 2 ≤
      (5120 * m + 2560) * (2 ^ m - 1) := by
  have hpow := fiveThousandOneHundredTwenty_mul_add_le_two_pow hm
  have hlinear : 5120 * m + 15360 ≤ 2 ^ m - 1 := by omega
  nlinarith

/-- Integral factorial-block recurrence for the base-256 normalization. -/
theorem strongCrowdingFactorialBlock_step {m : ℕ} (hm : 20 ≤ m) :
    (5120 * (m + 1) + 2560) ^ (2 ^ (m + 1)) *
        (2 ^ m - 2).factorial ≤
      (5120 * m + 2560) ^ (2 ^ m) *
        (2 ^ (m + 1) - 2).factorial := by
  let n := 2 ^ m
  have hn : 2 ≤ n := by
    dsimp [n]
    have hlarge : 2 ^ 20 ≤ 2 ^ m :=
      Nat.pow_le_pow_right (by omega) hm
    exact (by norm_num : 2 ≤ 2 ^ 20).trans hlarge
  have hbase : (5120 * (m + 1) + 2560) ^ 2 ≤
      (5120 * m + 2560) * (n - 1) := by
    simpa [n] using strongCrowdingBase_square_le hm
  have hpowBase := Nat.pow_le_pow_left hbase n
  have hfac0 := @Nat.factorial_mul_pow_le_factorial (n - 2) n
  have hfac : (n - 1) ^ n * (n - 2).factorial ≤
      (2 * n - 2).factorial := by
    have hfac' : (n - 2).factorial * (n - 1) ^ n ≤
        (2 * n - 2).factorial := by
      simpa [show n - 2 + 1 = n - 1 by omega,
        show n - 2 + n = 2 * n - 2 by omega] using hfac0
    simpa [Nat.mul_comm] using hfac'
  have hdouble : 2 ^ (m + 1) = 2 * n := by
    dsimp [n]
    rw [pow_succ]
    omega
  have hlargePow :
      (5120 * (m + 1) + 2560) ^ (2 ^ (m + 1)) =
        ((5120 * (m + 1) + 2560) ^ 2) ^ n := by
    rw [hdouble, pow_mul]
  calc
    (5120 * (m + 1) + 2560) ^ (2 ^ (m + 1)) *
          (2 ^ m - 2).factorial =
        ((5120 * (m + 1) + 2560) ^ 2) ^ n *
          (n - 2).factorial := by
      rw [hlargePow]
    _ ≤ ((5120 * m + 2560) * (n - 1)) ^ n *
        (n - 2).factorial := Nat.mul_le_mul_right _ hpowBase
    _ = (5120 * m + 2560) ^ n *
        ((n - 1) ^ n * (n - 2).factorial) := by
      rw [mul_pow]
      ac_rfl
    _ ≤ (5120 * m + 2560) ^ n * (2 * n - 2).factorial :=
      Nat.mul_le_mul_left _ hfac
    _ = (5120 * m + 2560) ^ (2 ^ m) *
        (2 ^ (m + 1) - 2).factorial := by
      rw [hdouble]

/-- Ford's crowding term after moving `256^(2^m)` to the numerator. -/
noncomputable def fordCrowdingStrongNormalizedTerm (m : ℕ) : ℝ :=
  ((5120 * m + 2560 : ℕ) : ℝ) ^ (2 ^ m) /
    (((2 ^ m - 2).factorial : ℕ) : ℝ)

theorem fordCrowdingStrongNormalizedTerm_anti_step
    {m : ℕ} (hm : 20 ≤ m) :
    fordCrowdingStrongNormalizedTerm (m + 1) ≤
      fordCrowdingStrongNormalizedTerm m := by
  have hstep := strongCrowdingFactorialBlock_step hm
  have hstepR :
      (((5120 * (m + 1) + 2560 : ℕ) : ℝ) ^ (2 ^ (m + 1))) *
          (((2 ^ m - 2).factorial : ℕ) : ℝ) ≤
        (((5120 * m + 2560 : ℕ) : ℝ) ^ (2 ^ m)) *
          (((2 ^ (m + 1) - 2).factorial : ℕ) : ℝ) := by
    exact_mod_cast hstep
  dsimp [fordCrowdingStrongNormalizedTerm]
  exact (div_le_div_iff₀ (by positivity :
      (0 : ℝ) < (((2 ^ (m + 1) - 2).factorial : ℕ) : ℝ))
    (by positivity :
      (0 : ℝ) < (((2 ^ m - 2).factorial : ℕ) : ℝ))).2 hstepR

/-- Explicit (large) constant absorbing the first twenty depths. -/
noncomputable def fordCrowdingStrongSuppressionConstant : ℝ :=
  (104960 : ℝ) ^ (2 ^ 20)

theorem fordCrowdingStrongSuppressionConstant_pos :
    0 < fordCrowdingStrongSuppressionConstant := by
  dsimp [fordCrowdingStrongSuppressionConstant]
  positivity

theorem fordCrowdingStrongNormalizedTerm_le_twenty
    {m : ℕ} (hm : 20 ≤ m) :
    fordCrowdingStrongNormalizedTerm m ≤
      fordCrowdingStrongNormalizedTerm 20 := by
  induction m, hm using Nat.le_induction with
  | base => exact le_rfl
  | succ m hm ih =>
      exact (fordCrowdingStrongNormalizedTerm_anti_step hm).trans ih

theorem fordCrowdingStrongNormalizedTerm_le (m : ℕ) :
    fordCrowdingStrongNormalizedTerm m ≤
      fordCrowdingStrongSuppressionConstant := by
  by_cases hm : m ≤ 20
  · have hbase : 5120 * m + 2560 ≤ 104960 := by omega
    have hexp : 2 ^ m ≤ 2 ^ 20 :=
      Nat.pow_le_pow_right (by omega) hm
    have hpowBase :
        (((5120 * m + 2560 : ℕ) : ℝ) ^ (2 ^ m)) ≤
          (104960 : ℝ) ^ (2 ^ m) := by
      exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast hbase) _
    have hpowExp : (104960 : ℝ) ^ (2 ^ m) ≤
        (104960 : ℝ) ^ (2 ^ 20) :=
      pow_le_pow_right₀ (by norm_num) hexp
    have hfac : (1 : ℝ) ≤
        (((2 ^ m - 2).factorial : ℕ) : ℝ) := by
      exact_mod_cast (Nat.factorial_pos (2 ^ m - 2))
    calc
      fordCrowdingStrongNormalizedTerm m ≤
          (((5120 * m + 2560 : ℕ) : ℝ) ^ (2 ^ m)) := by
        dsimp [fordCrowdingStrongNormalizedTerm]
        exact div_le_self (by positivity) hfac
      _ ≤ (104960 : ℝ) ^ (2 ^ m) := hpowBase
      _ ≤ fordCrowdingStrongSuppressionConstant := hpowExp
  · have h20 : 20 ≤ m := by omega
    apply (fordCrowdingStrongNormalizedTerm_le_twenty h20).trans
    have hfac : (1 : ℝ) ≤
        (((2 ^ 20 - 2).factorial : ℕ) : ℝ) := by
      exact_mod_cast (Nat.factorial_pos (2 ^ 20 - 2))
    change (104960 : ℝ) ^ (2 ^ 20) /
        (((2 ^ 20 - 2).factorial : ℕ) : ℝ) ≤
      (104960 : ℝ) ^ (2 ^ 20)
    exact div_le_self (by positivity) hfac

/-- The exponent-shifted factorial suppression required in Ford's passage
from (32h) to (33). -/
theorem fordCrowdingFactorialSuppression_shifted (m : ℕ) :
    (((20 * m + 10 : ℕ) : ℝ) ^ (2 ^ m)) /
        (((2 ^ m - 2).factorial : ℕ) : ℝ) ≤
      fordCrowdingStrongSuppressionConstant /
        (2 : ℝ) ^ (2 ^ (m + 3)) := by
  have h := fordCrowdingStrongNormalizedTerm_le m
  have h256 : (0 : ℝ) < (256 : ℝ) ^ (2 ^ m) := by positivity
  have hscaled :
      (((20 * m + 10 : ℕ) : ℝ) ^ (2 ^ m)) /
          (((2 ^ m - 2).factorial : ℕ) : ℝ) ≤
        fordCrowdingStrongSuppressionConstant /
          (256 : ℝ) ^ (2 ^ m) := by
    apply (le_div_iff₀ h256).2
    calc
      (((20 * m + 10 : ℕ) : ℝ) ^ (2 ^ m) /
            (((2 ^ m - 2).factorial : ℕ) : ℝ)) *
          (256 : ℝ) ^ (2 ^ m) =
          fordCrowdingStrongNormalizedTerm m := by
        dsimp [fordCrowdingStrongNormalizedTerm]
        rw [div_mul_eq_mul_div, ← mul_pow]
        congr 2
        push_cast
        ring
      _ ≤ fordCrowdingStrongSuppressionConstant := h
  have hden : (256 : ℝ) ^ (2 ^ m) =
      (2 : ℝ) ^ (2 ^ (m + 3)) := by
    calc
      (256 : ℝ) ^ (2 ^ m) = ((2 : ℝ) ^ 8) ^ (2 ^ m) := by norm_num
      _ = (2 : ℝ) ^ (8 * 2 ^ m) := by rw [pow_mul]
      _ = (2 : ℝ) ^ (2 ^ (m + 3)) := by
        congr 1
        rw [pow_add]
        norm_num
        omega
  rwa [hden] at hscaled

end Erdos446
