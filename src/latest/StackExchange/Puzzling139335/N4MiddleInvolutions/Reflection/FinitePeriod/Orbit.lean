import Mathlib.Analysis.Complex.Circle
import Mathlib.GroupTheory.OrderOfElement

/-! A finite multiplicatively invariant set detects finite rotation order. -/

open Set

namespace Puzzling139335.N4MiddleInvolutions.Reflection

/-- A rotation preserving a finite set that contains a nonzero complex
number has finite order. Only forward invariance of the set is needed. -/
theorem isOfFinOrder_of_finite_mul_invariant (s : Set ℂ) (hs : s.Finite)
    (a : Circle) (hrot : ∀ z ∈ s, (a : ℂ) * z ∈ s)
    {z : ℂ} (hz : z ∈ s) (hne : z ≠ 0) : IsOfFinOrder a := by
  have horbit : ∀ n : ℕ, (a : ℂ) ^ n * z ∈ s := by
    intro n
    induction n with
    | zero => simpa using hz
    | succ n ih => simpa only [pow_succ', mul_assoc] using hrot _ ih
  obtain ⟨m, n, hmn, hpow⟩ := hs.exists_lt_map_eq_of_forall_mem horbit
  have hcircle : a ^ m = a ^ n := by
    apply Circle.coe_injective
    simpa only [Circle.coe_pow] using mul_right_cancel₀ hne hpow
  refine isOfFinOrder_iff_pow_eq_one.mpr ⟨n - m, tsub_pos_iff_lt.mpr hmn, ?_⟩
  rw [← mul_left_cancel_iff (a := a ^ m), ← pow_add,
    add_tsub_cancel_of_le hmn.le, hcircle, mul_one]

/-- The same finite-orbit argument supplies a positive period explicitly. -/
theorem exists_positive_period_of_finite_mul_invariant (s : Set ℂ) (hs : s.Finite)
    (a : Circle) (hrot : ∀ z ∈ s, (a : ℂ) * z ∈ s)
    {z : ℂ} (hz : z ∈ s) (hne : z ≠ 0) :
    ∃ n : ℕ, 0 < n ∧ (a : ℂ) ^ n = 1 := by
  obtain ⟨n, hn, hpow⟩ :=
    (isOfFinOrder_of_finite_mul_invariant s hs a hrot hz hne).exists_pow_eq_one
  refine ⟨n, hn, ?_⟩
  simpa only [Circle.coe_pow, Circle.coe_one] using
    congrArg (fun b : Circle => (b : ℂ)) hpow

end Puzzling139335.N4MiddleInvolutions.Reflection
