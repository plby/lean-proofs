import StackExchange.Puzzling139335.N6.Triple
import StackExchange.Puzzling139335.N6.TwoDouble.Dispatch

/-!
# The six-incidence case

The actual corner incidences have exactly two possible patterns: one
three-way corner, or two double corners. Both are excluded from the
original Jordan-dissection hypotheses, with all intrinsic-type, local
boundary-germ, and placement reductions proved along the way.
-/

namespace Puzzling139335.SquareDissection

/-- A protected-center dissection with six corner incidences must have
two double corners and two uniquely owned corners. -/
theorem two_double_corners_of_six (d : SquareDissection) (hc : d.HasProtectedCenter)
    (hN : d.cornerIncidenceCount = 6) : N6.HasTwoDoubleCorners d := by
  rcases N6.corner_cases d hN with htriple | hdouble
  · exact (N6.not_hasProtectedCenter_of_triple_corner d hN htriple hc).elim
  · exact hdouble

/-- No corner has three owners in the six-incidence branch. -/
theorem cornerTileCount_le_two_of_six (d : SquareDissection) (hc : d.HasProtectedCenter)
    (hN : d.cornerIncidenceCount = 6) (j : Fin 4) : d.cornerTileCount j ≤ 2 := by
  obtain ⟨s, t, _, hs, ht, hother⟩ := d.two_double_corners_of_six hc hN
  by_cases hjs : j = s
  · subst j
    exact hs.le
  by_cases hjt : j = t
  · subst j
    exact ht.le
  rw [hother j hjs hjt]
  decide

/-- Six tile-corner incidences cannot occur in a square dissection having
a piece that contains a neighborhood of the center. -/
theorem not_hasProtectedCenter_of_six (d : SquareDissection)
    (hN : d.cornerIncidenceCount = 6) : ¬ d.HasProtectedCenter := by
  intro hc
  exact N6.TwoDouble.two_double_corner_impossible d hc hN
    (d.two_double_corners_of_six hc hN)

theorem cornerIncidenceCount_ne_six (d : SquareDissection) (hc : d.HasProtectedCenter) :
    d.cornerIncidenceCount ≠ 6 := fun hN => d.not_hasProtectedCenter_of_six hN hc

end Puzzling139335.SquareDissection
