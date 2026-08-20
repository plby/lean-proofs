/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos980.External.Erdos822.ShiftedTotientResidues

/-!
# A fixed-prime large-q incidence fiber

The preceding residue lemma reduces every nonempty large-q fiber, with
fixed small and middle factors, to one residue class.  This file combines
that reduction with the already checked reciprocal residue-class estimate.
-/

namespace Erdos822

open scoped BigOperators

/-- Uniform reciprocal estimate for the large primes q such that a fixed
prime p divides shiftedTotient (k*r*q), in the case p divides neither
fixed factor. -/
theorem exists_sum_inv_shiftedDivisibleLargePrimes_upper_bound :
    ∃ A C : ℝ, 1 ≤ A ∧ 0 < C ∧
      ∀ N p k r y S : ℕ,
        2 ≤ N → p.Prime → p ≤ N ^ 21 →
        k ∈ oddSmallFactors N → r ∈ middlePrimes N →
        ¬ p ∣ k → ¬ p ∣ r →
        2 ≤ y → y < N ^ 21 → 101 ≤ S →
        Real.log A ≤ 4 * (S - 100 : ℕ) / 99 →
        let eta := (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)
        let W :=
          (1 + eta) *
            (C * (Real.log (2 : ℝ) / Real.log (y : ℝ)) *
              Real.exp 3)
        let E := ((y ^ S : ℕ) : ℝ) ^ 2
        ∑ q ∈ shiftedDivisibleLargePrimes N p k r, (1 : ℝ) / q ≤
          (2 * W / (p : ℝ) + E / ((N ^ 21 : ℕ) : ℝ)) *
            (harmonic N : ℝ) := by
  obtain ⟨A, C, hA, hC, hclass⟩ :=
    exists_sum_inv_largePrimeResidueClass_upper_bound
  refine ⟨A, C, hA, hC, ?_⟩
  intro N p k r y S hN hp hpN hk hr hpk hpr hy hyN hS hlog
  dsimp only
  by_cases hne : (shiftedDivisibleLargePrimes N p k r).Nonempty
  · let q₀ := (shiftedDivisibleLargePrimes N p k r).min' hne
    have hsubset :
        shiftedDivisibleLargePrimes N p k r ⊆
          largePrimeResidueClass N p q₀ y := by
      exact shiftedDivisibleLargePrimes_subset_largePrimeResidueClass_of_nonempty
        hN hp hk hr hpk hpr hyN hne
    calc
      (∑ q ∈ shiftedDivisibleLargePrimes N p k r, (1 : ℝ) / q) ≤
          ∑ q ∈ largePrimeResidueClass N p q₀ y, (1 : ℝ) / q := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
        intro q hq hnot
        positivity
      _ ≤
          (2 *
              ((1 + (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)) *
                (C * (Real.log (2 : ℝ) / Real.log (y : ℝ)) *
                  Real.exp 3)) /
              (p : ℝ) +
            ((y ^ S : ℕ) : ℝ) ^ 2 / ((N ^ 21 : ℕ) : ℝ)) *
            (harmonic N : ℝ) := by
        exact hclass N p q₀ y S hN hp hpN hy hS hlog
  · have hempty : shiftedDivisibleLargePrimes N p k r = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hne
    rw [hempty]
    simp only [Finset.sum_empty]
    have hlog2 : 0 ≤ Real.log (2 : ℝ) :=
      Real.log_nonneg (by norm_num)
    have hlogy : 0 < Real.log (y : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < y by omega))
    have hharm : 0 ≤ (harmonic N : ℝ) := by
      rw [harmonic_eq_sum_Icc, Rat.cast_sum]
      exact Finset.sum_nonneg fun j hj => by positivity
    positivity

end Erdos822
