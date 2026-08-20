/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import BoundedGaps.Maynard.PrimeMertensInterval
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Reciprocal prime mass for Erdős Problem 822

The structured set in the GIL proof uses two prime variables in fixed
multiplicative intervals.  The bundled bounded-gaps development already
contains a fully proved bounded-error Mertens estimate for
`∑ log p / p`.  This file records the elementary passage to the unweighted
reciprocal sum that the later counting argument uses.
-/

namespace Erdos822

open Finset Nat Real

/-- A convenient name for the reciprocal mass of primes in `[w,z]`. -/
noncomputable def reciprocalPrimeIntervalSum (w z : ℕ) : ℝ :=
  ∑ p ∈ Nat.primesLE z \ Nat.primesLE (w - 1), (1 : ℝ) / p

/-- The log-weighted prime interval sum is at most `log z` times its
unweighted reciprocal mass. -/
theorem primeLogIntervalSum_le_log_mul_reciprocalPrimeIntervalSum
    {w z : ℕ} (hw : 2 ≤ w) (hwz : w ≤ z) :
    BoundedGaps.Maynard.primeLogIntervalSum w z ≤
      Real.log z * reciprocalPrimeIntervalSum w z := by
  have hzgt : 1 < z := lt_of_lt_of_le (by omega : 1 < w) hwz
  have hzpos : (0 : ℝ) < z := by exact_mod_cast (Nat.zero_lt_of_lt hzgt)
  unfold BoundedGaps.Maynard.primeLogIntervalSum reciprocalPrimeIntervalSum
  calc
    (∑ p ∈ Nat.primesLE z \ Nat.primesLE (w - 1),
        Real.log p / (p : ℝ)) ≤
        ∑ p ∈ Nat.primesLE z \ Nat.primesLE (w - 1),
          Real.log z * ((1 : ℝ) / p) := by
      apply Finset.sum_le_sum
      intro p hp
      have hpz : p ≤ z :=
        Nat.le_of_mem_primesLE (Finset.mem_sdiff.mp hp).1
      have hpprime : p.Prime :=
        Nat.prime_of_mem_primesLE (Finset.mem_sdiff.mp hp).1
      have hppos : (0 : ℝ) < p := by exact_mod_cast hpprime.pos
      have hlogle : Real.log p ≤ Real.log z :=
        Real.strictMonoOn_log.monotoneOn
          (by simp only [Set.mem_Ioi]; exact hppos)
          (by simp only [Set.mem_Ioi]; exact hzpos)
          (by exact_mod_cast hpz)
      calc
        Real.log p / (p : ℝ) = Real.log p * ((1 : ℝ) / p) := by ring
        _ ≤ Real.log z * ((1 : ℝ) / p) :=
          mul_le_mul_of_nonneg_right hlogle (by positivity)
    _ = Real.log z *
        ∑ p ∈ Nat.primesLE z \ Nat.primesLE (w - 1), (1 : ℝ) / p := by
      rw [Finset.mul_sum]

/-- A bounded-error lower bound for unweighted reciprocal prime mass on an
interval.  The constant is absolute because it is inherited from the proved
prime Mertens estimate in `BoundedGaps`. -/
theorem exists_reciprocalPrimeIntervalSum_lower :
    ∃ C : ℝ, ∀ {w z : ℕ}, 2 ≤ w → w ≤ z →
      (Real.log ((z : ℝ) / (w : ℝ)) - C) / Real.log z ≤
        reciprocalPrimeIntervalSum w z := by
  obtain ⟨C, hC⟩ :=
    BoundedGaps.Maynard.exists_uniform_abs_primeLogIntervalSum_sub_log_div
  refine ⟨C, fun {w z} hw hwz => ?_⟩
  have hzgt : 1 < z := lt_of_lt_of_le (by omega : 1 < w) hwz
  have hlogz : 0 < Real.log (z : ℝ) :=
    Real.log_pos (by exact_mod_cast hzgt)
  have habs := hC hw hwz
  have hbelow :
      Real.log ((z : ℝ) / (w : ℝ)) - C ≤
        BoundedGaps.Maynard.primeLogIntervalSum w z := by
    linarith [neg_le_abs
      (BoundedGaps.Maynard.primeLogIntervalSum w z -
        Real.log ((z : ℝ) / (w : ℝ)))]
  apply (div_le_iff₀ hlogz).2
  calc
    Real.log ((z : ℝ) / (w : ℝ)) - C ≤
        BoundedGaps.Maynard.primeLogIntervalSum w z := hbelow
    _ ≤ Real.log z * reciprocalPrimeIntervalSum w z :=
      primeLogIntervalSum_le_log_mul_reciprocalPrimeIntervalSum hw hwz
    _ = reciprocalPrimeIntervalSum w z * Real.log z := by ring

/-- The reciprocal mass of primes between the fourth and fifth powers is
eventually bounded below by an absolute positive constant.  These are the
integer-power versions of the exponents `1/15` and `1/12` after writing the
main scale as `N^60`. -/
theorem eventually_reciprocalPrimeIntervalSum_four_five_lower :
    ∀ᶠ N : ℕ in Filter.atTop,
      (1 / 10 : ℝ) ≤ reciprocalPrimeIntervalSum (N ^ 4) (N ^ 5) := by
  obtain ⟨C, hC⟩ := exists_reciprocalPrimeIntervalSum_lower
  have hlog := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
    (Filter.eventually_ge_atTop (2 * |C|))
  filter_upwards [hlog, Filter.eventually_ge_atTop 2] with N hlogN hN
  change 2 * |C| ≤ Real.log (N : ℝ) at hlogN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hlogNpos : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hw : 2 ≤ N ^ 4 :=
    (by norm_num : 2 ≤ 2 ^ 4).trans (Nat.pow_le_pow_left hN 4)
  have hwz : N ^ 4 ≤ N ^ 5 := by
    exact Nat.pow_le_pow_right (by omega : 1 ≤ N) (by omega)
  have hbase := hC hw hwz
  have hratio :
      Real.log (((N ^ 5 : ℕ) : ℝ) / ((N ^ 4 : ℕ) : ℝ)) =
        Real.log (N : ℝ) := by
    push_cast
    rw [Real.log_div (by positivity) (by positivity), Real.log_pow, Real.log_pow]
    ring
  have htop : Real.log ((N ^ 5 : ℕ) : ℝ) = 5 * Real.log (N : ℝ) := by
    push_cast
    rw [Real.log_pow]
    norm_num
  rw [hratio, htop] at hbase
  calc
    (1 / 10 : ℝ) ≤
        (Real.log (N : ℝ) - C) / (5 * Real.log (N : ℝ)) := by
      apply (le_div_iff₀ (by positivity)).2
      nlinarith [le_abs_self C]
    _ ≤ reciprocalPrimeIntervalSum (N ^ 4) (N ^ 5) := hbase

/-- The analogous positive reciprocal mass for the `q`-prime interval.
The exponents `21` and `22` encode `7/20` and `11/30` at scale `N^60`. -/
theorem eventually_reciprocalPrimeIntervalSum_twentyone_twentytwo_lower :
    ∀ᶠ N : ℕ in Filter.atTop,
      (1 / 50 : ℝ) ≤ reciprocalPrimeIntervalSum (N ^ 21) (N ^ 22) := by
  obtain ⟨C, hC⟩ := exists_reciprocalPrimeIntervalSum_lower
  have hlog := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
    (Filter.eventually_ge_atTop (2 * |C|))
  filter_upwards [hlog, Filter.eventually_ge_atTop 2] with N hlogN hN
  change 2 * |C| ≤ Real.log (N : ℝ) at hlogN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hlogNpos : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hw : 2 ≤ N ^ 21 :=
    (by norm_num : 2 ≤ 2 ^ 21).trans (Nat.pow_le_pow_left hN 21)
  have hwz : N ^ 21 ≤ N ^ 22 := by
    exact Nat.pow_le_pow_right (by omega : 1 ≤ N) (by omega)
  have hbase := hC hw hwz
  have hratio :
      Real.log (((N ^ 22 : ℕ) : ℝ) / ((N ^ 21 : ℕ) : ℝ)) =
        Real.log (N : ℝ) := by
    push_cast
    rw [Real.log_div (by positivity) (by positivity), Real.log_pow, Real.log_pow]
    ring
  have htop : Real.log ((N ^ 22 : ℕ) : ℝ) = 22 * Real.log (N : ℝ) := by
    push_cast
    rw [Real.log_pow]
    norm_num
  rw [hratio, htop] at hbase
  calc
    (1 / 50 : ℝ) ≤
        (Real.log (N : ℝ) - C) / (22 * Real.log (N : ℝ)) := by
      apply (le_div_iff₀ (by positivity)).2
      nlinarith [le_abs_self C]
    _ ≤ reciprocalPrimeIntervalSum (N ^ 21) (N ^ 22) := hbase

end Erdos822
