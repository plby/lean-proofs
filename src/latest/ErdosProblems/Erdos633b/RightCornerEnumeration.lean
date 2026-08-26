import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-! Finite arithmetic for the right-tile angle-inventory reduction.
All bounds and exclusions are proved by kernel-checked arithmetic. -/

namespace Erdos633b

theorem right_deficit_denominator_bound (A d p q r k : ℕ)
    (hA : 0 < A) (hA2 : A ≤ 2) (hpq : p < q) (hq : q ≤ 7)
    (he : d * (q + r) + A * p = 2 * d * k + A * q) : d ≤ 14 := by
  have hkr : 2 * k < q + r := by
    by_contra h
    have hh : q + r ≤ 2 * k := by omega
    have hm := Nat.mul_le_mul_left d hh
    have hp := Nat.mul_lt_mul_of_pos_left hpq hA
    nlinarith
  have hh : 2 * k + 1 ≤ q + r := by omega
  have hm := Nat.mul_le_mul_left d hh
  have hb : d + A * p ≤ A * q := by nlinarith
  have ha := Nat.mul_le_mul_right q hA2
  nlinarith

theorem right_corner_parameters_exhaustive (P Q R p q r k : ℕ)
    (hP : 4 ≤ P) (hP15 : P ≤ 15) (hQR : Q + R ≤ 1) (htotal : 5 ≤ P + Q + R)
    (hkp : 1 ≤ k) (hkb : k ≤ 2) (hpq : p < q) (hqb : q ≤ 7) (hrb : r ≤ 3)
    (he : (P - Q) * (q + r) + (2 - Q - R) * p =
      2 * (P - Q) * k + (2 - Q - R) * q) :
    (Q = 0 ∧ R = 0 ∧ (P = 5 ∨ P = 6 ∨ P = 8 ∨ P = 10)) ∨
    (Q = 1 ∧ R = 0 ∧ (P = 4 ∨ P = 5 ∨ P = 6)) ∨
    (Q = 0 ∧ R = 1 ∧ (P = 4 ∨ P = 5)) := by
  have hQ : Q ≤ 1 := by omega
  have hR : R ≤ 1 := by omega
  interval_cases Q <;> interval_cases R
  · left
    refine ⟨rfl, rfl, ?_⟩
    interval_cases P <;> omega
  · right; right
    refine ⟨rfl, rfl, ?_⟩
    interval_cases P <;> omega
  · right; left
    refine ⟨rfl, rfl, ?_⟩
    interval_cases P <;> omega
  · omega

end Erdos633b
