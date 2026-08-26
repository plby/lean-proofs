/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierPinnedUnconditionalDistribution

/-!
# Exact prime-interval lower bounds from Chebyshev endpoints

The half-open endpoints and integer subtractions are retained. The
Chebyshev theta difference is the literal sum of logarithms of the
primes in the interval, giving a direct count lower bound from its
two endpoint errors.
-/

namespace Erdos4b

noncomputable section

open scoped BigOperators

theorem sum_log_auxiliaryPrimeInterval_eq_theta_sub
    {A B : ℕ} (hA : 0 < A) (hAB : A ≤ B) :
    (∑ p ∈ auxiliaryPrimeInterval A B, Real.log p) =
      Chebyshev.theta (B - 1 : ℕ) - Chebyshev.theta (A - 1 : ℕ) := by
  have hB : 0 < B := hA.trans_le hAB
  unfold auxiliaryPrimeInterval
  rw [Chebyshev.theta_eq_sum_primesLE_log, Chebyshev.theta_eq_sum_primesLE_log,
    Nat.primesLE_eq_filter_range, Nat.primesLE_eq_filter_range]
  simp only [Finset.sum_filter, Nat.sub_add_cancel hA, Nat.sub_add_cancel hB]
  exact Finset.sum_Ico_eq_sub _ hAB

theorem theta_sub_le_log_mul_primeInterval_card
    {A B : ℕ} (hA : 0 < A) (hAB : A ≤ B) :
    Chebyshev.theta (B - 1 : ℕ) - Chebyshev.theta (A - 1 : ℕ) ≤
      Real.log B * (auxiliaryPrimeInterval A B).card := by
  rw [← sum_log_auxiliaryPrimeInterval_eq_theta_sub hA hAB]
  calc
    _ ≤ ∑ p ∈ auxiliaryPrimeInterval A B, Real.log B := by
      apply Finset.sum_le_sum
      intro p hp
      obtain ⟨hpA, hpB, hprime⟩ := mem_auxiliaryPrimeInterval.mp hp
      apply Real.log_le_log (by exact_mod_cast hprime.pos)
      exact_mod_cast hpB.le
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, mul_comm]

theorem interval_length_sub_theta_errors_le_log_mul_primeCount
    {A B : ℕ} (hA : 0 < A) (hAB : A ≤ B) :
    ((B : ℝ) - A) - |Chebyshev.theta (B - 1 : ℕ) - (B - 1 : ℕ)| -
        |Chebyshev.theta (A - 1 : ℕ) - (A - 1 : ℕ)| ≤
      Real.log B * (auxiliaryPrimeInterval A B).card := by
  have hB : 0 < B := hA.trans_le hAB
  have hdiff : ((B - 1 : ℕ) : ℝ) - (A - 1 : ℕ) = (B : ℝ) - A := by
    rw [Nat.cast_sub hB, Nat.cast_sub hA, Nat.cast_one]
    ring
  have hupper := theta_sub_le_log_mul_primeInterval_card hA hAB
  have heB := neg_abs_le (Chebyshev.theta (B - 1 : ℕ) - (B - 1 : ℕ))
  have heA := le_abs_self (Chebyshev.theta (A - 1 : ℕ) - (A - 1 : ℕ))
  linarith

end

end Erdos4b
