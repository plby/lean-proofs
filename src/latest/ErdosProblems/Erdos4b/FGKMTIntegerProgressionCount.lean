/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib.Data.Int.CardIntervalMod
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# An absolute interval error for an integer residue class

The count is the difference of two ceilings. Each ceiling differs from
its argument by a number in `[0,1)`, so the count differs from interval
length divided by the modulus by at most one, independently of every
endpoint, residue and modulus.
-/

namespace Erdos4b.FGKMT

noncomputable section

theorem integerProgressionCount_error (a b r v : ℤ) (hab : a ≤ b) (hr : 0 < r) :
    |(((Finset.Ico a b).filter (fun n => n ≡ v [ZMOD r])).card : ℝ) -
      ((b : ℝ) - a) / r| ≤ 1 := by
  let A : ℚ := ((a : ℚ) - v) / r
  let B : ℚ := ((b : ℚ) - v) / r
  have hAB : A ≤ B := div_le_div_of_nonneg_right
    (sub_le_sub_right (by exact_mod_cast hab) _) (by exact_mod_cast hr.le)
  have hceil : ⌈A⌉ ≤ ⌈B⌉ := Int.ceil_mono hAB
  have hc := Int.Ico_filter_modEq_card a b hr v
  change (((Finset.Ico a b).filter (fun n => n ≡ v [ZMOD r])).card : ℤ) =
    max (⌈B⌉ - ⌈A⌉) 0 at hc
  rw [max_eq_left (sub_nonneg.mpr hceil)] at hc
  have hcQ : (((Finset.Ico a b).filter (fun n => n ≡ v [ZMOD r])).card : ℚ) =
      (⌈B⌉ : ℚ) - (⌈A⌉ : ℚ) := by exact_mod_cast hc
  have hd : B - A = ((b : ℚ) - a) / r := by dsimp only [A, B]; ring
  have hbQ :
      |(((Finset.Ico a b).filter (fun n => n ≡ v [ZMOD r])).card : ℚ) -
        ((b : ℚ) - a) / r| ≤ 1 := by
    rw [hcQ, ← hd, abs_le]
    constructor <;> linarith [Int.le_ceil A, Int.ceil_lt_add_one A,
      Int.le_ceil B, Int.ceil_lt_add_one B]
  exact_mod_cast hbQ

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.integerProgressionCount_error
