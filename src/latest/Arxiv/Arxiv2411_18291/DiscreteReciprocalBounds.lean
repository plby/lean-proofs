import Arxiv.Arxiv2411_18291.DiscretePowerBounds
import Mathlib.Tactic.FieldSimp

/-! # Explicit finite differences for reciprocal comparison errors -/

namespace Arxiv2411_18291

theorem reciprocal_difference_identity {s p : ℝ} (hs : 0 < s) (hp : 0 < p) :
    1 / s - 1 / p = (p - s) / (p * s) := by
  field_simp

theorem reciprocal_difference_bounds {s p : ℝ} (hs : 0 < s) (hsp : s ≤ p)
    (hhalf : p ≤ 2 * s) :
    (p - s) / p ^ 2 ≤ 1 / s - 1 / p ∧
      1 / s - 1 / p ≤ 2 * (p - s) / p ^ 2 := by
  have hp : 0 < p := hs.trans_le hsp
  have hd : 0 ≤ p - s := sub_nonneg.mpr hsp
  rw [reciprocal_difference_identity hs hp]
  constructor
  · apply div_le_div_of_nonneg_left hd (mul_pos hp hs)
    simpa only [pow_two] using mul_le_mul_of_nonneg_left hsp hp.le
  · apply (div_le_div_iff₀ (mul_pos hp hs) (pow_pos hp 2)).mpr
    have h := mul_le_mul_of_nonneg_left hhalf (mul_nonneg hp.le hd)
    nlinarith only [h]

theorem reciprocal_square_difference_bounds {s p : ℝ} (hs : 0 < s) (hsp : s ≤ p)
    (hhalf : p ≤ 2 * s) :
    2 * (p - s) / p ^ 3 ≤ (1 / s) ^ 2 - (1 / p) ^ 2 ∧
      (1 / s) ^ 2 - (1 / p) ^ 2 ≤ 8 * (p - s) / p ^ 3 := by
  have hp : 0 < p := hs.trans_le hsp
  have hd : 0 ≤ p - s := sub_nonneg.mpr hsp
  have horder : 1 / p ≤ 1 / s := one_div_le_one_div_of_le hs hsp
  have hupper : 1 / s ≤ 2 / p := (div_le_div_iff₀ hs hp).mpr (by simpa using hhalf)
  obtain ⟨hilow, hihigh⟩ := reciprocal_difference_bounds hs hsp hhalf
  obtain ⟨hlow, hhigh⟩ := real_pow_difference_bounds (by positivity : 0 ≤ 1 / p) horder 2
  norm_num only [Nat.cast_ofNat, Nat.reduceSub, pow_one] at hlow hhigh
  constructor
  · calc
      _ = 2 * (1 / p) * ((p - s) / p ^ 2) := by ring
      _ ≤ 2 * (1 / p) * (1 / s - 1 / p) :=
        mul_le_mul_of_nonneg_left hilow (by positivity)
      _ ≤ _ := hlow
  · calc
      _ ≤ 2 * (1 / s) * (1 / s - 1 / p) := hhigh
      _ ≤ (2 * (2 / p)) * (2 * (p - s) / p ^ 2) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hupper (by norm_num)) hihigh
          (sub_nonneg.mpr horder) (by positivity)
      _ = _ := by ring

end Arxiv2411_18291
