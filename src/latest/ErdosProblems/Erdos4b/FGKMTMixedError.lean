/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-! # Combining one distinguished-coordinate error with a tensor error -/

namespace Erdos4b.FGKMT

theorem mixed_error_from_head_tail {Q S a P ε : ℝ} {j : ℕ}
    (ha : 0 ≤ a) (hP : 0 < P) (hε : 0 ≤ ε) (hj : (j : ℝ) * ε ≤ 1)
    (hhead : |Q - a * S| ≤ a * ε * S)
    (htail : |S - P| ≤ (2 * (j : ℝ) * ε) * P) :
    |Q - a * P| ≤ (4 * ((j : ℝ) + 1) * ε) * (a * P) := by
  have hSP : S ≤ 3 * P := by
    have hsmall : 2 * (j : ℝ) * ε ≤ 2 := by nlinarith
    have hb := (le_abs_self (S - P)).trans htail
    have hc := mul_le_mul_of_nonneg_right hsmall hP.le
    linarith
  calc
    _ = |(Q - a * S) + a * (S - P)| := by congr 1; ring
    _ ≤ |Q - a * S| + |a * (S - P)| := abs_add_le _ _
    _ ≤ a * ε * S + a * ((2 * (j : ℝ) * ε) * P) := by
      rw [abs_mul, abs_of_nonneg ha]
      exact add_le_add hhead (mul_le_mul_of_nonneg_left htail ha)
    _ ≤ a * ε * (3 * P) + a * ((2 * (j : ℝ) * ε) * P) :=
      add_le_add (mul_le_mul_of_nonneg_left hSP (mul_nonneg ha hε)) le_rfl
    _ = (3 + 2 * (j : ℝ)) * ε * (a * P) := by ring
    _ ≤ _ := by
      have hc : 3 + 2 * (j : ℝ) ≤ 4 * ((j : ℝ) + 1) := by
        nlinarith [show (0 : ℝ) ≤ j from Nat.cast_nonneg j]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc hε) (mul_nonneg ha hP.le)

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.mixed_error_from_head_tail
