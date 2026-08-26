import ErdosProblems.Erdos633b.NegativeCubic

/-! Nonsquareness of every count supplied by the positive case-(6) construction. -/

namespace Erdos633b

theorem case_six_rational_nonsquare (a b c : ℚ) (ha : 0 < a) (hac : a < c)
    (he : b * c + a ^ 2 = c ^ 2) : ¬ IsSquare ((c + b) * (2 * c + b)) := by
  have hc : 0 < c := ha.trans hac
  have hc0 : c ≠ 0 := ne_of_gt hc
  let s := a / c
  have hs : 0 < s := div_pos ha hc
  have hs1 : s < 1 := (div_lt_one hc).mpr hac
  have hs2 : s ^ 2 < 2 := by nlinarith
  have hid : (c + b) * (2 * c + b) = c ^ 2 * ((2 - s ^ 2) * (3 - s ^ 2)) := by
    dsimp [s]
    field_simp
    linear_combination (b * c - a ^ 2 + 4 * c ^ 2) * he
  intro hS
  rw [hid] at hS
  exact case_six_parameter_nonsquare s hs2 ((isSquare_sq_mul_iff c _ hc0).mp hS)

theorem case_six_integer_nonsquare (a b c : ℕ) (ha : 0 < a) (hac : a < c)
    (he : b * c + a ^ 2 = c ^ 2) : ¬ IsSquare ((c + b) * (2 * c + b)) := by
  intro hs
  apply case_six_rational_nonsquare a b c (by exact_mod_cast ha) (by exact_mod_cast hac)
    (by exact_mod_cast he)
  have hh := Rat.isSquare_natCast_iff.mpr hs
  simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using hh

end Erdos633b
