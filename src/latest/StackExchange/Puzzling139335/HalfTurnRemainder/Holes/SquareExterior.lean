import StackExchange.Puzzling139335.ExteriorContact.Square

/-!
# The connected, unbounded square exterior

These wrappers identify the complement of the closed unit square with the
unbounded region of its Jordan boundary.
-/

open Set

namespace Puzzling139335

/-- The complement of the closed unit square is connected. -/
theorem isConnected_compl_unitSquare : IsConnected unitSquareᶜ := by
  simpa only [outside_frontier_unitSquare] using
    (Schoenflies.jordan_curve_theorem isJordanCurve_frontier_unitSquare).isConnected_outside

/-- The complement of the closed unit square is preconnected. -/
theorem isPreconnected_compl_unitSquare : IsPreconnected unitSquareᶜ :=
  isConnected_compl_unitSquare.isPreconnected

/-- The complement of the closed unit square is unbounded. -/
theorem not_isBounded_compl_unitSquare : ¬ Bornology.IsBounded unitSquareᶜ := by
  simpa only [outside_frontier_unitSquare] using
    (Schoenflies.jordan_curve_theorem isJordanCurve_frontier_unitSquare).not_isBounded_outside

end Puzzling139335
