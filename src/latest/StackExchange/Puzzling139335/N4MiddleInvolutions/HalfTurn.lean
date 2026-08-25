import StackExchange.Puzzling139335.N4MiddleInvolutions.HalfTurn.Core
import StackExchange.Puzzling139335.N4MiddleInvolutions.BoundaryBalance

/-!
# An arbitrary-center half-turn cannot relate the two middle pieces

This statement uses only the actual normalized outer-pair configuration
and protected-center hypothesis. In particular, it assumes no convexity,
rectifiability, Jordan property of the union, or special interface shape.
-/

open Set

namespace Puzzling139335.N4MiddleInvolutions

theorem halfTurn_middle_impossible {d : SquareDissection}
    (h : N4OuterPair.Configuration d) (hc : d.HasProtectedCenter) (C : Plane)
    (hpair : AffineIsometryEquiv.pointReflection ℝ C '' d.piece 2 = d.piece 3) :
    False := by
  obtain ⟨S⟩ := HalfTurn.exists_left_source h hc hpair
  apply HalfTurn.false_of_left_source h hc hpair S
  intro a b hab
  rcases HalfTurn.outer_half_arm h hc hpair with hleft | hright
  · exact BoundaryBalance.middle_interface_not_subset_segment_of_full_left_arm
      h hc hleft hab
  · exact BoundaryBalance.middle_interface_not_subset_segment_of_full_right_arm
      h hc hright hab

end Puzzling139335.N4MiddleInvolutions
