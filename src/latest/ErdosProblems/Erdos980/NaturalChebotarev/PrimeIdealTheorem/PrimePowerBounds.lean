/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Sqrt

/-!
# Elementary bounds for higher prime powers

This file contains the arithmetic estimates used to bound the contribution
of prime powers in the passage from a von-Mangoldt sum to a Chebyshev sum.
Nothing here depends on primality: the base is merely assumed to be at least
two.
-/

namespace Erdos980.NaturalChebotarev.PrimeIdealTheorem

open scoped BigOperators

noncomputable section

/-- Taking real logarithms of `q ^ m ≤ N` gives the expected bound on the
exponent.  The assumption `2 ≤ q` also guarantees that all logarithms in the
monotonicity argument have positive inputs. -/
theorem exponent_mul_log_le_log_of_pow_le
    {q m N : ℕ} (hq : 2 ≤ q) (hpow : q ^ m ≤ N) :
    (m : ℝ) * Real.log (q : ℝ) ≤ Real.log (N : ℝ) := by
  have hqpos_nat : 0 < q := by omega
  have hq_one : 1 ≤ q := by omega
  have hN_one : 1 ≤ N := (one_le_pow₀ hq_one).trans hpow
  have hpow_real : (q : ℝ) ^ m ≤ (N : ℝ) := by
    exact_mod_cast hpow
  have hqpow_mem : (q : ℝ) ^ m ∈ Set.Ioi (0 : ℝ) := by
    change (0 : ℝ) < (q : ℝ) ^ m
    exact pow_pos (by exact_mod_cast hqpos_nat) m
  have hN_mem : (N : ℝ) ∈ Set.Ioi (0 : ℝ) := by
    change (0 : ℝ) < (N : ℝ)
    exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 1) hN_one)
  have hlog := Real.strictMonoOn_log.monotoneOn hqpow_mem hN_mem hpow_real
  simpa only [Real.log_pow] using hlog

/-- The integral version of the exponent bound. -/
theorem exponent_le_natLog_of_pow_le
    {q m N : ℕ} (hq : 2 ≤ q) (hpow : q ^ m ≤ N) :
    m ≤ Nat.log q N := by
  exact Nat.le_log_of_pow_le (by omega) hpow

/-- A power with exponent at least two can only occur below the square-root
cutoff for its base. -/
theorem base_le_sqrt_of_sqExponent_pow_le
    {q m N : ℕ} (hq : 2 ≤ q) (hm : 2 ≤ m) (hpow : q ^ m ≤ N) :
    q ≤ Nat.sqrt N := by
  rw [Nat.le_sqrt']
  exact (Nat.pow_le_pow_right (by omega) hm).trans hpow

/-- Finite set of all positive exponents whose `q`-power is at most `N`.
The range bound is only present to obtain a `Finset`; it is shown below not
to discard any positive exponent when `q ≥ 2`. -/
def positivePowerExponents (q N : ℕ) : Finset ℕ :=
  (Finset.range (N + 1)).filter fun m ↦ 1 ≤ m ∧ q ^ m ≤ N

/-- Membership in `positivePowerExponents` has no residual range condition. -/
theorem mem_positivePowerExponents_iff
    {q N m : ℕ} (hq : 2 ≤ q) :
    m ∈ positivePowerExponents q N ↔ 1 ≤ m ∧ q ^ m ≤ N := by
  constructor
  · intro hm
    exact (Finset.mem_filter.mp hm).2
  · intro hm
    rcases hm with ⟨hmpos, hpow⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr ?_, ⟨hmpos, hpow⟩⟩
    have hm_le_pow : m ≤ q ^ m :=
      Nat.lt_two_pow_self.le.trans (Nat.pow_le_pow_left hq m)
    exact Nat.lt_succ_iff.mpr (hm_le_pow.trans hpow)

/-- There are at most `log_q N` positive exponents with `q ^ m ≤ N`. -/
theorem card_positivePowerExponents_le_natLog
    {q N : ℕ} (hq : 2 ≤ q) :
    (positivePowerExponents q N).card ≤ Nat.log q N := by
  calc
    (positivePowerExponents q N).card ≤
        (Finset.Icc 1 (Nat.log q N)).card := by
      apply Finset.card_le_card
      intro m hm
      rw [Finset.mem_Icc]
      have hm' := (mem_positivePowerExponents_iff hq).mp hm
      exact ⟨hm'.1, exponent_le_natLog_of_pow_le hq hm'.2⟩
    _ = Nat.log q N := by
      rw [Nat.card_Icc]
      omega

/-- Sum of the logarithmic base weight over all positive admissible
exponents. -/
def powerExponentLogWeight (q N : ℕ) : ℝ :=
  ∑ _m ∈ positivePowerExponents q N, Real.log (q : ℝ)

theorem powerExponentLogWeight_eq_card_mul (q N : ℕ) :
    powerExponentLogWeight q N =
      ((positivePowerExponents q N).card : ℝ) * Real.log (q : ℝ) := by
  simp [powerExponentLogWeight, nsmul_eq_mul]

/-- For a fixed base, the total logarithmic weight of all of its positive
powers up to `N` is at most `log N`. -/
theorem powerExponentLogWeight_le_log
    {q N : ℕ} (hq : 2 ≤ q) :
    powerExponentLogWeight q N ≤ Real.log (N : ℝ) := by
  by_cases hN : N = 0
  · subst N
    have hset : positivePowerExponents q 0 = ∅ := by
      ext m
      simp only [Finset.notMem_empty, iff_false]
      rw [mem_positivePowerExponents_iff hq]
      intro hm
      have hq_one : 1 ≤ q := by omega
      have : 1 ≤ 0 := (one_le_pow₀ hq_one).trans hm.2
      omega
    simp [powerExponentLogWeight, hset]
  · have hcard : ((positivePowerExponents q N).card : ℝ) ≤
        (Nat.log q N : ℝ) := by
      exact_mod_cast card_positivePowerExponents_le_natLog hq
    have hlog_nonneg : 0 ≤ Real.log (q : ℝ) :=
      Real.log_nonneg (by exact_mod_cast (show 1 ≤ q by omega))
    have hcard_weight := mul_le_mul_of_nonneg_right hcard hlog_nonneg
    have hmaxpow : q ^ Nat.log q N ≤ N :=
      Nat.pow_le_of_le_log hN le_rfl
    rw [powerExponentLogWeight_eq_card_mul]
    exact hcard_weight.trans
      (exponent_mul_log_le_log_of_pow_le hq hmaxpow)

/-- The exponents contributing genuine higher powers. -/
def higherPowerExponents (q N : ℕ) : Finset ℕ :=
  (positivePowerExponents q N).filter fun m ↦ 2 ≤ m

theorem mem_higherPowerExponents_iff
    {q N m : ℕ} (hq : 2 ≤ q) :
    m ∈ higherPowerExponents q N ↔ 2 ≤ m ∧ q ^ m ≤ N := by
  simp only [higherPowerExponents, Finset.mem_filter,
    mem_positivePowerExponents_iff hq]
  omega

/-- Every base supporting a genuine higher power lies below `sqrt N`. -/
theorem base_le_sqrt_of_mem_higherPowerExponents
    {q N m : ℕ} (hq : 2 ≤ q) (hm : m ∈ higherPowerExponents q N) :
    q ≤ Nat.sqrt N := by
  have hm' := (mem_higherPowerExponents_iff hq).mp hm
  exact base_le_sqrt_of_sqExponent_pow_le hq hm'.1 hm'.2

/-- The total fixed-base weight of the genuine higher powers is also bounded
by `log N`. -/
theorem higherPowerExponentLogWeight_le_log
    {q N : ℕ} (hq : 2 ≤ q) :
    (∑ _m ∈ higherPowerExponents q N, Real.log (q : ℝ)) ≤
      Real.log (N : ℝ) := by
  calc
    (∑ _m ∈ higherPowerExponents q N, Real.log (q : ℝ)) ≤
        powerExponentLogWeight q N := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro m hm
        exact (Finset.mem_filter.mp hm).1
      · intro m _ _
        exact Real.log_nonneg (by exact_mod_cast (show 1 ≤ q by omega))
    _ ≤ Real.log (N : ℝ) := powerExponentLogWeight_le_log hq

end

end Erdos980.NaturalChebotarev.PrimeIdealTheorem
