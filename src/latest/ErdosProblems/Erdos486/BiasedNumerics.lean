import Mathlib

/- Ported to Lean/Mathlib 4.33.0; see README.md for source and modifications. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Exact numerical inequalities for the biased finite block

All estimates are over `ℚ`, so the later finite counting argument uses no
floating-point approximations or transcendental inequalities.
-/

namespace Erdos486

/-- A crude exponential bound that absorbs the linear collision factor. -/
theorem six_mul_le_two_pow_four_mul_add_two (r : ℕ) :
    6 * r ≤ 2 ^ (4 * r + 2) := by
  induction r with
  | zero => norm_num
  | succ r ih =>
      rw [show 4 * (r + 1) + 2 = (4 * r + 2) + 4 by omega, pow_add]
      norm_num
      have hpow : 0 < 2 ^ (4 * r + 2) := by positivity
      omega

theorem six_mul_two_pow_le (r : ℕ) :
    6 * r * 2 ^ (2 * r) ≤ 2 ^ (6 * r + 2) := by
  calc
    6 * r * 2 ^ (2 * r) ≤ 2 ^ (4 * r + 2) * 2 ^ (2 * r) :=
      Nat.mul_le_mul_right _ (six_mul_le_two_pow_four_mul_add_two r)
    _ = 2 ^ (6 * r + 2) := by
      rw [← pow_add]
      congr 1
      omega

/-- The union-bound collision term is absorbed by one copy of the target
geometric error. -/
theorem collision_numeric_le (r : ℕ) :
    ((6 * r : ℕ) : ℚ) / (2 : ℚ) ^ (6 * r + 2) ≤
      ((63 : ℚ) / 64) ^ (2 * r) := by
  have hpowpos : (0 : ℚ) < (2 : ℚ) ^ (6 * r + 2) := by positivity
  have htwo :
      ((6 * r : ℕ) : ℚ) / (2 : ℚ) ^ (6 * r + 2) ≤
        1 / (2 : ℚ) ^ (2 * r) := by
    rw [div_le_div_iff₀ hpowpos (by positivity : (0 : ℚ) < (2 : ℚ) ^ (2 * r))]
    simp only [one_mul]
    exact_mod_cast six_mul_two_pow_le r
  calc
    ((6 * r : ℕ) : ℚ) / (2 : ℚ) ^ (6 * r + 2) ≤
        1 / (2 : ℚ) ^ (2 * r) := htwo
    _ = ((1 : ℚ) / 2) ^ (2 * r) := by
      rw [div_pow]
      simp
    _ ≤ ((63 : ℚ) / 64) ^ (2 * r) :=
      pow_le_pow_left₀ (by norm_num) (by norm_num) _

/-- Markov's bad-anchor term is no larger than the target error. -/
theorem bad_anchor_numeric_le (r : ℕ) :
    ((125 : ℚ) / 128) ^ (2 * r) ≤
      ((63 : ℚ) / 64) ^ (2 * r) := by
  exact pow_le_pow_left₀ (by norm_num) (by norm_num) _

/-- The weighted good-anchor sum is no larger than the target error. -/
theorem weighted_good_numeric_le (r : ℕ) :
    (2 : ℚ) ^ (2 * r) * ((25 : ℚ) / 32) ^ (6 * r) ≤
      ((63 : ℚ) / 64) ^ (2 * r) := by
  have h25 :
      ((25 : ℚ) / 32) ^ (6 * r) =
        (((25 : ℚ) / 32) ^ 3) ^ (2 * r) := by
    calc
      ((25 : ℚ) / 32) ^ (6 * r) =
          ((25 : ℚ) / 32) ^ (3 * (2 * r)) := by
        congr 1
        omega
      _ = (((25 : ℚ) / 32) ^ 3) ^ (2 * r) := pow_mul _ _ _
  calc
    (2 : ℚ) ^ (2 * r) * ((25 : ℚ) / 32) ^ (6 * r) =
        (2 : ℚ) ^ (2 * r) * (((25 : ℚ) / 32) ^ 3) ^ (2 * r) := by
      rw [h25]
    _ = ((2 : ℚ) * (((25 : ℚ) / 32) ^ 3)) ^ (2 * r) :=
      (mul_pow (2 : ℚ) (((25 : ℚ) / 32) ^ 3) (2 * r)).symm
    _ =
        ((15625 : ℚ) / 16384) ^ (2 * r) := by
      norm_num
    _ ≤ ((63 : ℚ) / 64) ^ (2 * r) :=
      pow_le_pow_left₀ (by norm_num) (by norm_num) _

/-- The complete collision/bad-anchor/good-anchor budget. -/
theorem three_error_terms_le_eta (r : ℕ)
    {collision bad good : ℚ}
    (hcollision : collision ≤ ((63 : ℚ) / 64) ^ (2 * r))
    (hbad : bad ≤ ((63 : ℚ) / 64) ^ (2 * r))
    (hgood : good ≤ ((63 : ℚ) / 64) ^ (2 * r)) :
    collision + bad + good ≤
      3 * ((63 : ℚ) / 64) ^ (2 * r) := by
  linarith

end Erdos486
