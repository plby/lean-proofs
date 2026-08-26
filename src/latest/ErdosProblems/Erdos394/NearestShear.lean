import Mathlib

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Centered integer remainder by nearest-integer rounding
-/

namespace Erdos394

/-- Any integer can be reduced modulo a nonzero integer to absolute value at
most half the modulus. -/
theorem exists_int_shear_natAbs_le_half (x a : ℤ) (ha : a ≠ 0) :
    ∃ n : ℤ, 2 * (x - n * a).natAbs ≤ a.natAbs := by
  let n : ℤ := round ((x : ℝ) / (a : ℝ))
  refine ⟨n, ?_⟩
  have haR : (a : ℝ) ≠ 0 := by exact_mod_cast ha
  have hr := abs_sub_round ((x : ℝ) / (a : ℝ))
  have hin : ((x - n * a : ℤ) : ℝ) =
      (a : ℝ) * ((x : ℝ) / (a : ℝ) - (n : ℝ)) := by
    rw [Int.cast_sub, Int.cast_mul]
    field_simp [haR]
  have hid : |((x - n * a : ℤ) : ℝ)| =
      |(a : ℝ)| * |(x : ℝ) / (a : ℝ) - (n : ℝ)| := by
    rw [hin, abs_mul]
  have hreal : 2 * |((x - n * a : ℤ) : ℝ)| ≤ |(a : ℝ)| := by
    rw [hid]
    have haabs : 0 ≤ |(a : ℝ)| := abs_nonneg _
    nlinarith [mul_le_mul_of_nonneg_left hr haabs]
  have hcast : (2 * (x - n * a).natAbs : ℝ) ≤ (a.natAbs : ℝ) := by
    push_cast
    simpa [Int.natCast_natAbs, Int.cast_abs] using hreal
  exact_mod_cast hcast

end Erdos394
