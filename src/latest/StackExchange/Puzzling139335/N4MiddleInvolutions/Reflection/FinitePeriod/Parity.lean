import Mathlib.Analysis.Complex.Circle
import Mathlib.GroupTheory.OrderOfElement

/-! The parity alternative for a rotation of finite order. -/

namespace Puzzling139335.N4MiddleInvolutions.Reflection

/-- A rotation of finite order either has a power equal to the half-turn,
or has an odd positive period. -/
theorem negative_power_or_odd_period (a : Circle) (hfin : IsOfFinOrder a) :
    (∃ k : ℕ, (a : ℂ) ^ k = -1) ∨ ∃ m : ℕ, (a : ℂ) ^ (2 * m + 1) = 1 := by
  have hpos := hfin.orderOf_pos
  have hperiod : (a : ℂ) ^ orderOf a = 1 := by
    simpa only [Circle.coe_pow, Circle.coe_one] using
      congrArg ((↑) : Circle → ℂ) (pow_orderOf_eq_one a)
  by_cases heven : orderOf a % 2 = 0
  · have horder : orderOf a = orderOf a / 2 * 2 := by omega
    have hk0 : orderOf a / 2 ≠ 0 := by omega
    have hklt : orderOf a / 2 < orderOf a := by omega
    have hne : (a : ℂ) ^ (orderOf a / 2) ≠ 1 := by
      intro hone
      apply pow_ne_one_of_lt_orderOf hk0 hklt
      apply Circle.ext
      simpa only [Circle.coe_pow, Circle.coe_one] using hone
    have hsq : ((a : ℂ) ^ (orderOf a / 2)) ^ 2 = 1 := by
      rw [← pow_mul, ← horder]
      exact hperiod
    exact Or.inl ⟨orderOf a / 2, (sq_eq_one_iff.mp hsq).resolve_left hne⟩
  · have horder : orderOf a = 2 * (orderOf a / 2) + 1 := by omega
    refine Or.inr ⟨orderOf a / 2, ?_⟩
    rw [← horder]
    exact hperiod

end Puzzling139335.N4MiddleInvolutions.Reflection
