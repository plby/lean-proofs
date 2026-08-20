/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.SieveDensity
import BoundedGaps.Maynard.PrimeMertens

/-!
# Erdős Problem 446: logarithmically weighted prime moments

This file records the elementary prime-log estimates used when the finite
Ford families are summed over their prime labels.  The first moment is exactly
the prime Mertens sum already proved in `BoundedGaps`.  Higher moments cost at
most the corresponding power of the endpoint logarithm.
-/

namespace Erdos446

open Finset Real
open scoped BigOperators

noncomputable section

/-- The `r`-th logarithmic prime moment up to `P`. -/
def primeLogMoment (r P : ℕ) : ℝ :=
  ∑ p ∈ primesUpTo P, Real.log (p : ℝ) ^ r / (p : ℝ)

/-- The logarithmically weighted prime mass used in Ford's block sums. -/
def weightedPrimeLogMass (P : ℕ) : ℝ :=
  ∑ p ∈ primesUpTo P, Real.log (p : ℝ) / (p : ℝ)

theorem weightedPrimeLogMass_eq_primeLogMoment_one (P : ℕ) :
    weightedPrimeLogMass P = primeLogMoment 1 P := by
  unfold weightedPrimeLogMass primeLogMoment
  simp

/-- Our cutoff convention agrees with Mathlib's `Nat.primesLE`. -/
theorem primesUpTo_eq_primesLE_for_primeLogMass (P : ℕ) :
    primesUpTo P = Nat.primesLE P := by
  ext p
  simp only [primesUpTo, Finset.mem_filter, Finset.mem_Icc,
    Nat.mem_primesLE]
  constructor
  · rintro ⟨⟨hp2, hpP⟩, hp⟩
    exact ⟨hpP, hp⟩
  · rintro ⟨hpP, hp⟩
    exact ⟨⟨hp.two_le, hpP⟩, hp⟩

/-- The weighted mass is exactly the prime-log harmonic sum from
`BoundedGaps.Maynard.PrimeMertens`. -/
theorem weightedPrimeLogMass_eq_primeLogHarmonicSum (P : ℕ) :
    weightedPrimeLogMass P =
      BoundedGaps.Maynard.primeLogHarmonicSum P := by
  unfold weightedPrimeLogMass BoundedGaps.Maynard.primeLogHarmonicSum
  rw [primesUpTo_eq_primesLE_for_primeLogMass]

theorem weightedPrimeLogMass_nonneg (P : ℕ) :
    0 ≤ weightedPrimeLogMass P := by
  unfold weightedPrimeLogMass
  exact Finset.sum_nonneg fun p hp ↦ by positivity

/-- A single positive constant bounds the first prime-log moment by `log P`.
The constant is obtained explicitly from the bounded-error prime Mertens
constant and `log 2 > 0`. -/
theorem exists_pos_weightedPrimeLogMass_le_log :
    ∃ C : ℝ, 0 < C ∧ ∀ P : ℕ, 2 ≤ P →
      weightedPrimeLogMass P ≤ C * Real.log (P : ℝ) := by
  obtain ⟨C₀, hC₀⟩ :=
    BoundedGaps.Maynard.exists_uniform_abs_primeLogHarmonicSum_sub_log
  let C : ℝ := 1 + |C₀| / Real.log 2
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hCpos : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨C, hCpos, fun P hP ↦ ?_⟩
  have hPReal : (2 : ℝ) ≤ (P : ℝ) := by exact_mod_cast hP
  have hlog2P : Real.log (2 : ℝ) ≤ Real.log (P : ℝ) :=
    Real.strictMonoOn_log.monotoneOn
      (by simp only [Set.mem_Ioi]; norm_num)
      (by simp only [Set.mem_Ioi]; positivity) hPReal
  have hMertens :
      BoundedGaps.Maynard.primeLogHarmonicSum P ≤
        Real.log (P : ℝ) + C₀ := by
    linarith [le_abs_self
      (BoundedGaps.Maynard.primeLogHarmonicSum P - Real.log (P : ℝ)),
      hC₀ P]
  have hC₀abs : C₀ ≤ |C₀| := le_abs_self C₀
  have habsBound :
      |C₀| ≤ (|C₀| / Real.log 2) * Real.log (P : ℝ) := by
    calc
      |C₀| = (|C₀| / Real.log 2) * Real.log 2 := by field_simp
      _ ≤ (|C₀| / Real.log 2) * Real.log (P : ℝ) := by
        exact mul_le_mul_of_nonneg_left hlog2P (by positivity)
  rw [weightedPrimeLogMass_eq_primeLogHarmonicSum]
  dsimp [C]
  nlinarith

/-- Every positive logarithmic moment is controlled by the first moment and
the largest possible logarithm in the cutoff interval. -/
theorem primeLogMoment_le_log_pow_mul_mass {r P : ℕ} (hr : 1 ≤ r) :
    primeLogMoment r P ≤
      Real.log (P : ℝ) ^ (r - 1) * weightedPrimeLogMass P := by
  unfold primeLogMoment weightedPrimeLogMass
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hp
  have hpData := Finset.mem_filter.mp hp
  have hpPrime : p.Prime := hpData.2
  have hpP : p ≤ P := (Finset.mem_Icc.mp hpData.1).2
  have hlogp : 0 ≤ Real.log (p : ℝ) := Real.log_natCast_nonneg p
  have hlogP : 0 ≤ Real.log (P : ℝ) := Real.log_natCast_nonneg P
  have hlogle : Real.log (p : ℝ) ≤ Real.log (P : ℝ) := by
    exact Real.strictMonoOn_log.monotoneOn
      (by simp only [Set.mem_Ioi]; exact_mod_cast hpPrime.pos)
      (by simp only [Set.mem_Ioi]; exact_mod_cast hpPrime.pos.trans_le hpP)
      (by exact_mod_cast hpP)
  have hpow :
      Real.log (p : ℝ) ^ (r - 1) ≤
        Real.log (P : ℝ) ^ (r - 1) :=
    pow_le_pow_left₀ hlogp hlogle _
  have hnum :
      Real.log (p : ℝ) ^ r ≤
        Real.log (P : ℝ) ^ (r - 1) * Real.log (p : ℝ) := by
    rw [show r = (r - 1) + 1 by omega, pow_succ]
    exact mul_le_mul_of_nonneg_right hpow hlogp
  calc
    Real.log (p : ℝ) ^ r / (p : ℝ) ≤
        (Real.log (P : ℝ) ^ (r - 1) * Real.log (p : ℝ)) /
          (p : ℝ) :=
      (div_le_div_iff_of_pos_right (by exact_mod_cast hpPrime.pos)).2 hnum
    _ = Real.log (P : ℝ) ^ (r - 1) *
        (Real.log (p : ℝ) / (p : ℝ)) := by ring

theorem primeLogMoment_two_le : ∀ P : ℕ,
    primeLogMoment 2 P ≤
      Real.log (P : ℝ) ^ (2 - 1) * weightedPrimeLogMass P := by
  intro P
  exact primeLogMoment_le_log_pow_mul_mass (P := P) (by norm_num)

theorem primeLogMoment_three_le : ∀ P : ℕ,
    primeLogMoment 3 P ≤
      Real.log (P : ℝ) ^ (3 - 1) * weightedPrimeLogMass P := by
  intro P
  exact primeLogMoment_le_log_pow_mul_mass (P := P) (by norm_num)

end

end Erdos446
