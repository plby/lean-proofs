import ErdosProblems.Erdos633.EulerCubics

/-!
# Unconditional arithmetic for the Y and U₂ tilings

Both square assumptions give rational points on cubic curves. The first
lands directly on Euler's curve; the second uses an explicit rational map
to the companion curve. The maps are checked as polynomial identities.
-/

namespace Erdos633

theorem rational_twisted_cubic_no_unit_interval (x y : ℚ)
    (hx0 : 0 < x) (hx1 : x < 1) (h : y ^ 2 = 3 * (x ^ 3 + 1)) : False := by
  have hx : x ≠ 0 := ne_of_gt hx0
  let X : ℚ := (x ^ 3 + 4) / (3 * x ^ 2)
  let Y : ℚ := y * (x ^ 3 - 8) / (9 * x ^ 3)
  have hraw : (y * (x ^ 3 - 8)) ^ 2 = 3 * ((x ^ 3 + 4) ^ 3 - 27 * x ^ 6) := by
    linear_combination (x ^ 3 - 8) ^ 2 * h
  have hcurve : Y ^ 2 = X ^ 3 - 1 := by
    dsimp [X, Y]
    field_simp
    linear_combination 27 * hraw
  have hX := (euler_rational_cubic_sub_one X Y hcurve).1
  have hden : 3 * x ^ 2 ≠ 0 := mul_ne_zero (by norm_num) (pow_ne_zero 2 hx)
  have heq : x ^ 3 + 4 = 3 * x ^ 2 := by
    have h' := (div_eq_iff hden).mp hX
    simpa only [one_mul] using h'
  have hprod := mul_pos (sub_pos.mpr hx1) (show 0 < 1 + x by linarith)
  have hx3 := pow_pos hx0 3
  nlinarith only [heq, hprod, hx3]

theorem oneTwenty_Y_ratio_not_isSquare (a b c : ℚ) (ha : 0 < a) (hb : 0 < b)
    (hconic : c ^ 2 = a ^ 2 + a * b + b ^ 2) :
    ¬ IsSquare ((a + b) * (2 * a + b)) := by
  rintro ⟨d, hd⟩
  have hs : 0 < a + b := add_pos ha hb
  have hs0 : a + b ≠ 0 := ne_of_gt hs
  have hu0 : 0 < a / (a + b) := div_pos ha hs
  have hu1 : a / (a + b) < 1 := (div_lt_one hs).mpr (by linarith)
  have hraw : (c * d) ^ 2 = a ^ 3 * (a + b) + (a + b) ^ 4 := by
    linear_combination d ^ 2 * hconic - (a ^ 2 + a * b + b ^ 2) * hd
  apply rational_cubic_add_one_no_unit_interval (a / (a + b)) (c * d / (a + b) ^ 2) hu0 hu1
  field_simp
  linear_combination hraw

theorem oneTwenty_U_two_ratio_not_isSquare (a b c : ℚ) (ha : 0 < a) (hb : 0 < b)
    (hconic : c ^ 2 = a ^ 2 + a * b + b ^ 2) :
    ¬ IsSquare (3 * (a + b) * (a + 2 * b)) := by
  rintro ⟨d, hd⟩
  have hs : 0 < a + b := add_pos ha hb
  have hs0 : a + b ≠ 0 := ne_of_gt hs
  have hu0 : 0 < b / (a + b) := div_pos hb hs
  have hu1 : b / (a + b) < 1 := (div_lt_one hs).mpr (by linarith)
  have hraw : (c * d) ^ 2 = 3 * (b ^ 3 * (a + b) + (a + b) ^ 4) := by
    linear_combination d ^ 2 * hconic - (a ^ 2 + a * b + b ^ 2) * hd
  apply rational_twisted_cubic_no_unit_interval (b / (a + b)) (c * d / (a + b) ^ 2) hu0 hu1
  field_simp
  linear_combination hraw

theorem oneTwenty_Y_numerator_not_isSquare (a b c : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hconic : c ^ 2 = a ^ 2 + a * b + b ^ 2) :
    ¬ IsSquare ((a + b) * (2 * a + b)) := by
  intro hsq
  apply oneTwenty_Y_ratio_not_isSquare (a : ℚ) b c
    (by exact_mod_cast ha) (by exact_mod_cast hb) (by exact_mod_cast hconic)
  have h := Rat.isSquare_natCast_iff.mpr hsq
  simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat] using h

theorem oneTwenty_U_two_numerator_not_isSquare (a b c : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hconic : c ^ 2 = a ^ 2 + a * b + b ^ 2) :
    ¬ IsSquare (3 * (a + b) * (a + 2 * b)) := by
  intro hsq
  apply oneTwenty_U_two_ratio_not_isSquare (a : ℚ) b c
    (by exact_mod_cast ha) (by exact_mod_cast hb) (by exact_mod_cast hconic)
  have h := Rat.isSquare_natCast_iff.mpr hsq
  simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat] using h

end Erdos633
