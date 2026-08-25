import BoundedGaps.Maynard.ImprovedGPY.SquareWeights
import BoundedGaps.Maynard.ImprovedGPY.SieveSums
import BoundedGaps.Maynard.ImprovedGPY.Positivity
import Mathlib.Tactic

/-! # Extracting many prime shifts without discarding the congruence -/

namespace MaynardBFT

open BoundedGaps.Maynard
open scoped BigOperators

theorem prime_shifts_in_residue_of_excess_pos
    {H : Finset ℕ} {N v W m : ℕ} {D : Finset (H → ℕ)}
    {lambda : (H → ℕ) → ℝ}
    (hpos : 0 < sieveExcess H N (m - 1 : ℕ)
      (preSievedSquareDivisorWeight H D lambda v W)) :
    ∃ n ∈ Finset.Ico N (2 * N), m ≤ BoundedGaps.primeShiftCount H n ∧ n ≡ v [MOD W] := by
  classical
  let w := preSievedSquareDivisorWeight H D lambda v W
  have hw : ∀ n, 0 ≤ w n := fun n => preSievedSquareDivisorWeight_nonneg _ _ _ _ _ _
  have hsum : 0 < ∑ n ∈ Finset.Ico N (2 * N),
      ((BoundedGaps.primeShiftCount H n : ℝ) - (m - 1 : ℕ)) * w n := by
    simpa only [← sieveExcess_eq_sum] using hpos
  by_contra hnone
  push Not at hnone
  have hterm : ∀ n ∈ Finset.Ico N (2 * N),
      ((BoundedGaps.primeShiftCount H n : ℝ) - (m - 1 : ℕ)) * w n ≤ 0 := by
    intro n hn
    by_cases hc : m ≤ BoundedGaps.primeShiftCount H n
    · have hnotmod : ¬n ≡ v [MOD W] := fun hm => hnone n hn hc hm
      have hwzero : w n = 0 := by simp [w, preSievedSquareDivisorWeight, hnotmod]
      rw [hwzero, mul_zero]
    · have hcReal : (BoundedGaps.primeShiftCount H n : ℝ) ≤ (m - 1 : ℕ) := by
        exact_mod_cast (by omega : BoundedGaps.primeShiftCount H n ≤ m - 1)
      exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hcReal) (hw n)
  exact (not_lt_of_ge (Finset.sum_nonpos hterm)) hsum

end MaynardBFT
