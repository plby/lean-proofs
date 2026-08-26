/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos822.SquarefreeCoefficientFilter

/-!
# Reciprocal mass of one prime-square shifted fiber

Once p is absent from the fixed factors k and r, the q-values for which
p² divides the shifted coefficient occupy a single class modulo p².
The elementary arbitrary-modulus block bound therefore gives the required
inverse-square saving.
-/

namespace Erdos822

open scoped BigOperators

theorem sum_inv_shiftedSquareDivisibleLargePrimes_le
    {N p k r y : ℕ} (hN : 2 ≤ N) (hp : p.Prime)
    (hk : k ∈ oddSmallFactors N) (hr : r ∈ middlePrimes N)
    (hpk : ¬ p ∣ k) (hpr : ¬ p ∣ r) (hy : y < N ^ 21) :
    ∑ q ∈ shiftedSquareDivisibleLargePrimes N p k r,
        (1 : ℝ) / q ≤
      ((1 : ℝ) / (p ^ 2 : ℕ) + (1 : ℝ) / (N ^ 21 : ℕ)) *
        (harmonic N : ℝ) := by
  classical
  by_cases hne :
      (shiftedSquareDivisibleLargePrimes N p k r).Nonempty
  · let q₀ := (shiftedSquareDivisibleLargePrimes N p k r).min' hne
    have hsubset :
        shiftedSquareDivisibleLargePrimes N p k r ⊆
          largePrimeResidueClass N (p ^ 2) q₀ y := by
      simpa [q₀] using
        (shiftedSquareDivisibleLargePrimes_subset_largePrimeResidueClass
          hN hp hk hr hpk hpr hy hne)
    calc
      (∑ q ∈ shiftedSquareDivisibleLargePrimes N p k r,
          (1 : ℝ) / q) ≤
          ∑ q ∈ largePrimeResidueClass N (p ^ 2) q₀ y,
            (1 : ℝ) / q := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
        intro q hq hnot
        positivity
      _ ≤ ((1 : ℝ) / (p ^ 2 : ℕ) +
            (1 : ℝ) / (N ^ 21 : ℕ)) *
          (harmonic N : ℝ) :=
        sum_inv_largePrimeResidueClass_le_harmonic_of_pos hN
          (pow_pos hp.pos 2)
  · have hempty : shiftedSquareDivisibleLargePrimes N p k r = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hne
    rw [hempty]
    simp only [Finset.sum_empty]
    have hH : 0 ≤ (harmonic N : ℝ) := by
      rw [harmonic_eq_sum_Icc, Rat.cast_sum]
      exact Finset.sum_nonneg fun j hj => by positivity
    exact mul_nonneg (by positivity) hH

end Erdos822
