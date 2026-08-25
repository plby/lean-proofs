/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos822.FixedPrimeIncidence
import ErdosProblems.Erdos822.PrimeReciprocal

/-!
# Upper bounds for reciprocal prime masses

The bundled prime-Mertens estimate controls the log-weighted prime sum.
On [w,z], every log p is at least log w, so division by log w gives a
uniform upper bound for the unweighted reciprocal mass.  The fixed power
intervals used in the odd cofactor layer are therefore eventually bounded
by one.
-/

namespace Erdos822

open scoped BigOperators

/-- The left endpoint logarithm times reciprocal prime mass is bounded by
the log-weighted prime interval sum. -/
theorem log_mul_reciprocalPrimeIntervalSum_le_primeLogIntervalSum
    {w z : ℕ} (hw : 2 ≤ w) (hwz : w ≤ z) :
    Real.log w * reciprocalPrimeIntervalSum w z ≤
      BoundedGaps.Maynard.primeLogIntervalSum w z := by
  have hwpos : (0 : ℝ) < w := by exact_mod_cast (by omega : 0 < w)
  unfold reciprocalPrimeIntervalSum
  unfold BoundedGaps.Maynard.primeLogIntervalSum
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hp
  have hpdata := Finset.mem_sdiff.mp hp
  have hpprime := Nat.prime_of_mem_primesLE hpdata.1
  have hpz := Nat.le_of_mem_primesLE hpdata.1
  have hwp : w ≤ p := by
    by_contra hnot
    have hpw : p ≤ w - 1 := by omega
    exact hpdata.2 (Nat.mem_primesLE.mpr ⟨hpw, hpprime⟩)
  have hppos : (0 : ℝ) < p := by exact_mod_cast hpprime.pos
  have hlogle : Real.log (w : ℝ) ≤ Real.log (p : ℝ) :=
    Real.strictMonoOn_log.monotoneOn
      (by simp only [Set.mem_Ioi]; exact hwpos)
      (by simp only [Set.mem_Ioi]; exact hppos)
      (by exact_mod_cast hwp)
  calc
    Real.log (w : ℝ) * ((1 : ℝ) / p) ≤
        Real.log (p : ℝ) * ((1 : ℝ) / p) :=
      mul_le_mul_of_nonneg_right hlogle (by positivity)
    _ = Real.log p / (p : ℝ) := by ring

/-- Uniform upper bound for reciprocal prime mass on one interval. -/
theorem exists_reciprocalPrimeIntervalSum_upper :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {w z : ℕ}, 2 ≤ w → w ≤ z →
      reciprocalPrimeIntervalSum w z ≤
        (Real.log ((z : ℝ) / (w : ℝ)) + C) / Real.log w := by
  obtain ⟨C, hC⟩ :=
    BoundedGaps.Maynard.exists_uniform_abs_primeLogIntervalSum_sub_log_div
  refine ⟨|C|, abs_nonneg C, fun {w z} hw hwz => ?_⟩
  have hlogw : 0 < Real.log (w : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < w by omega))
  have habs := hC hw hwz
  have htop :
      BoundedGaps.Maynard.primeLogIntervalSum w z ≤
        Real.log ((z : ℝ) / (w : ℝ)) + |C| := by
    linarith [le_abs_self
      (BoundedGaps.Maynard.primeLogIntervalSum w z -
        Real.log ((z : ℝ) / (w : ℝ))),
      le_abs_self
      (BoundedGaps.Maynard.primeLogIntervalSum w z -
        Real.log ((z : ℝ) / (w : ℝ))),
      le_abs_self C]
  apply (le_div_iff₀ hlogw).2
  simpa [mul_comm] using
    (log_mul_reciprocalPrimeIntervalSum_le_primeLogIntervalSum hw hwz).trans htop

/-- The middle-prime reciprocal mass is eventually at most one. -/
theorem eventually_reciprocalPrimeIntervalSum_four_five_upper_one :
    ∀ᶠ N : ℕ in Filter.atTop,
      reciprocalPrimeIntervalSum (N ^ 4) (N ^ 5) ≤ 1 := by
  obtain ⟨C, hC, hupper⟩ := exists_reciprocalPrimeIntervalSum_upper
  have hlog := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
    (Filter.eventually_ge_atTop C)
  filter_upwards [hlog, Filter.eventually_ge_atTop 2] with N hlogN hN
  change C ≤ Real.log (N : ℝ) at hlogN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hlogNpos : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hw : 2 ≤ N ^ 4 :=
    (by norm_num : 2 ≤ 2 ^ 4).trans (Nat.pow_le_pow_left hN 4)
  have hwz : N ^ 4 ≤ N ^ 5 :=
    Nat.pow_le_pow_right (by omega : 1 ≤ N) (by omega)
  have hbase := hupper hw hwz
  have hratio :
      Real.log (((N ^ 5 : ℕ) : ℝ) / ((N ^ 4 : ℕ) : ℝ)) =
        Real.log (N : ℝ) := by
    push_cast
    rw [Real.log_div (by positivity) (by positivity), Real.log_pow, Real.log_pow]
    ring
  have hden : Real.log ((N ^ 4 : ℕ) : ℝ) =
      4 * Real.log (N : ℝ) := by
    push_cast
    rw [Real.log_pow]
    norm_num
  rw [hratio, hden] at hbase
  calc
    reciprocalPrimeIntervalSum (N ^ 4) (N ^ 5) ≤
        (Real.log (N : ℝ) + C) / (4 * Real.log (N : ℝ)) := hbase
    _ ≤ 1 := by
      apply (div_le_iff₀ (by positivity)).2
      nlinarith

/-- The large-prime reciprocal mass is eventually at most one. -/
theorem eventually_reciprocalPrimeIntervalSum_twentyone_twentytwo_upper_one :
    ∀ᶠ N : ℕ in Filter.atTop,
      reciprocalPrimeIntervalSum (N ^ 21) (N ^ 22) ≤ 1 := by
  obtain ⟨C, hC, hupper⟩ := exists_reciprocalPrimeIntervalSum_upper
  have hlog := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
    (Filter.eventually_ge_atTop C)
  filter_upwards [hlog, Filter.eventually_ge_atTop 2] with N hlogN hN
  change C ≤ Real.log (N : ℝ) at hlogN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hlogNpos : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hw : 2 ≤ N ^ 21 :=
    (by norm_num : 2 ≤ 2 ^ 21).trans (Nat.pow_le_pow_left hN 21)
  have hwz : N ^ 21 ≤ N ^ 22 :=
    Nat.pow_le_pow_right (by omega : 1 ≤ N) (by omega)
  have hbase := hupper hw hwz
  have hratio :
      Real.log (((N ^ 22 : ℕ) : ℝ) / ((N ^ 21 : ℕ) : ℝ)) =
        Real.log (N : ℝ) := by
    push_cast
    rw [Real.log_div (by positivity) (by positivity), Real.log_pow, Real.log_pow]
    ring
  have hden : Real.log ((N ^ 21 : ℕ) : ℝ) =
      21 * Real.log (N : ℝ) := by
    push_cast
    rw [Real.log_pow]
    norm_num
  rw [hratio, hden] at hbase
  calc
    reciprocalPrimeIntervalSum (N ^ 21) (N ^ 22) ≤
        (Real.log (N : ℝ) + C) / (21 * Real.log (N : ℝ)) := hbase
    _ ≤ 1 := by
      apply (div_le_iff₀ (by positivity)).2
      nlinarith

end Erdos822
