import StackExchange.Puzzling139335.N4MiddleInvolutions.Reflection.FinitePeriod.Orbit
import StackExchange.Puzzling139335.N4MiddleInvolutions.Reflection.FinitePeriod.Parity

/-!
# Finite normal orbits give a half-turn or an odd period

These are purely complex-algebraic consequences of a finite invariant set
containing a nonzero member. They use no geometric or trigonometric hypotheses.
-/

open Set

namespace Puzzling139335.N4MiddleInvolutions.Reflection

/-- A finite invariant nonzero orbit forces either a half-turn power or an
odd positive period. -/
theorem negative_power_or_odd_period_of_finite_mul_invariant
    (s : Set ℂ) (hs : s.Finite) (a : Circle)
    (hrot : ∀ z ∈ s, (a : ℂ) * z ∈ s)
    {z : ℂ} (hz : z ∈ s) (hne : z ≠ 0) :
    (∃ k : ℕ, (a : ℂ) ^ k = -1) ∨ ∃ m : ℕ, (a : ℂ) ^ (2 * m + 1) = 1 :=
  negative_power_or_odd_period a (isOfFinOrder_of_finite_mul_invariant s hs a hrot hz hne)

end Puzzling139335.N4MiddleInvolutions.Reflection
