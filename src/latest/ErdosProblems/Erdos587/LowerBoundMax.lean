import ErdosProblems.Erdos587.LowerBound
import ErdosProblems.Erdos587.NVDevelopment

/-! The lower bound for the exact finite supremum used in the problem statement. -/

namespace Erdos587

theorem cube_root_div_four_le_maxNotSqSum (N : ℕ) (hN : 64 ≤ N) :
    (N : ℝ) ^ (1 / 3 : ℝ) / 4 ≤ (MaxNotSqSum N : ℝ) := by
  obtain ⟨A, hAN, hcard, hfree⟩ := exists_cube_root_square_sum_free N hN
  apply hcard.trans
  apply Nat.cast_le.mpr
  apply card_le_maxNotSqSum hAN
  intro S hSA hS
  exact hfree S hSA (Finset.nonempty_iff_ne_empty.mpr hS)

theorem lower_bound (N : ℕ) (hN : 64 ≤ N) :
    Real.nthRoot 3 (N : ℝ) / 4 ≤ (MaxNotSqSum N : ℝ) := by
  rw [nthRoot_three_natCast]
  simpa only [one_div] using cube_root_div_four_le_maxNotSqSum N hN

end Erdos587
