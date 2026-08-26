import Mathlib.Tactic

/-! Explicit constants for cleaning and absorbing into the two cores. -/

namespace Erdos556

theorem two_core_parameters (L b : ℕ) (hL : 200 ≤ L) (hb : 1 ≤ b)
    (hsmall : 100000 * b ≤ L) :
    0 < L / 100 ∧
    24 * b * L ≤ (L / 100) * (L / 10) ∧
    24 * b + L / 10 + 2 * (L / 100) + 1 ≤ L / 4 ∧
    4 * (L / 4) < 2 * L - L / 4 ∧
    L / 4 + 2 * (L / 100 + 1) ≤ 2 * L - L / 4 ∧
    (2 * L - L / 4) + L / 4 = 2 * L := by
  have hrt : 24 * b * L ≤ (L / 100) * (L / 10) := by
    have hr : 480 * b ≤ L / 100 := by omega
    have ht : L ≤ 20 * (L / 10) := by omega
    calc
      24 * b * L ≤ 24 * b * (20 * (L / 10)) := Nat.mul_le_mul_left _ ht
      _ = (480 * b) * (L / 10) := by ring
      _ ≤ (L / 100) * (L / 10) := Nat.mul_le_mul_right _ hr
  exact ⟨by omega, hrt, by omega, by omega, by omega, by omega⟩

end Erdos556
