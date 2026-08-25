import BoundedGaps.PrimeNumberTheorem.Analytic.PrimeCounting
import ErdosProblems.Erdos964.PrimeSliceCounts

/-!
# An unconditional prime-counting error envelope for the prime slices
-/

namespace Erdos964

open Asymptotics Filter
open scoped Asymptotics

theorem exists_primeCounting_relative_error (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      |(Nat.primeCounting n : ℝ) - (n : ℝ) / Real.log n| ≤ ε * ((n : ℝ) / Real.log n) := by
  have h := BoundedGaps.PrimeNumberTheorem.primeCounting_natCast_isEquivalent
  rw [Asymptotics.IsEquivalent] at h
  have hevent := h.bound hε
  obtain ⟨N, hN⟩ := eventually_atTop.mp hevent
  refine ⟨max N 2, le_max_right _ _, ?_⟩
  intro n hn
  have herr := hN n ((le_max_left N 2).trans hn)
  have hnonneg : 0 ≤ (n : ℝ) / Real.log n := div_nonneg (Nat.cast_nonneg n)
    (Real.log_natCast_nonneg n)
  simpa only [Pi.sub_apply, Real.norm_eq_abs, abs_of_nonneg hnonneg] using herr

end Erdos964
