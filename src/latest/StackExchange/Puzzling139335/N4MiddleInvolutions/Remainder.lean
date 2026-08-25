import StackExchange.Puzzling139335.N4MiddleInvolutions.Basic
import StackExchange.Puzzling139335.N4Remainder.Topology

/-! # The actual Jordan remainder for involutive middle congruences -/

open Set

namespace Puzzling139335.N4MiddleInvolutions

theorem outer_not_halfTurn_of_middle_involution {d : SquareDissection}
    (h : N4OuterPair.Configuration d) (hc : d.HasProtectedCenter)
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (hinv : Function.Involutive e)
    (he : e '' d.piece 2 = d.piece 3) :
    AffineIsometryEquiv.pointReflection ℝ squareCenter '' d.piece 0 ≠ d.piece 1 :=
  fun houter => false_of_outer_halfTurn_and_middle_involution h hc houter e hinv he

theorem middleUnion_jordan_of_involution {d : SquareDissection}
    (h : N4OuterPair.Configuration d) (hc : d.HasProtectedCenter)
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (hinv : Function.Involutive e)
    (he : e '' d.piece 2 = d.piece 3) : IsJordanRegion (middleUnion d) :=
  h.middle_union_jordan_of_no_outer_halfTurn hc
    (outer_not_halfTurn_of_middle_involution h hc e hinv he)

theorem middle_inter_isArcBetween_of_involution {d : SquareDissection}
    (h : N4OuterPair.Configuration d) (hc : d.HasProtectedCenter)
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (hinv : Function.Involutive e)
    (he : e '' d.piece 2 = d.piece 3) :
    ∃ p q : Plane, Schoenflies.IsArcBetween (d.piece 2 ∩ d.piece 3) p q :=
  h.middle_inter_isArcBetween_of_no_outer_halfTurn hc
    (outer_not_halfTurn_of_middle_involution h hc e hinv he)

theorem middle_inter_nontrivial_of_involution {d : SquareDissection}
    (h : N4OuterPair.Configuration d) (hc : d.HasProtectedCenter)
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (hinv : Function.Involutive e)
    (he : e '' d.piece 2 = d.piece 3) : (d.piece 2 ∩ d.piece 3).Nontrivial :=
  h.middle_inter_nontrivial_of_no_outer_halfTurn hc
    (outer_not_halfTurn_of_middle_involution h hc e hinv he)

end Puzzling139335.N4MiddleInvolutions
