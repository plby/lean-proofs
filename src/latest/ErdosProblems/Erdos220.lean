/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos220.Basic
import ErdosProblems.Erdos220.ConcreteGaps
import ErdosProblems.Erdos220.MomentExpansion
import ErdosProblems.Erdos220.SmoothRough

/-!
# Erdős Problem 220

Montgomery and Vaughan proved that the sum of the squares of consecutive
gaps between the positive reduced residues modulo `n` is bounded by an
absolute constant times `n² / φ(n)`.  The list `sortedTotatives n` is the
literal increasing list from the problem statement.  At `n = 1` this list is
empty (whereas `Nat.totient 1 = 1`), so its adjacent-gap sum is correctly
interpreted as the empty sum.
-/

open scoped BigOperators

namespace Erdos220

/-- The affirmative resolution of Erdős Problem 220, with `≪` expressed by
one positive real constant independent of the modulus. -/
theorem erdos_220 :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      (sumSquaredGaps (sortedTotatives n) : ℝ) ≤
        C * (n : ℝ) ^ 2 / (n.totient : ℝ) := by
  obtain ⟨B, hB, hEmpty⟩ := exists_emptyWindows_bound
  refine ⟨5 + 2 * B, by positivity, ?_⟩
  intro n hn
  by_cases hn1 : n = 1
  · subst n
    simpa using (show (0 : ℝ) ≤ 5 + 2 * B by positivity)
  · have hn2 : 2 ≤ n := by omega
    rw [cast_sumSquaredGaps_sortedTotatives hn2]
    exact gapSquareSum_le_of_emptyWindows_bound n (by omega) B hB.le
      (fun h hh hhn ↦ hEmpty (by omega) hh)

end Erdos220

#print axioms Erdos220.erdos_220
