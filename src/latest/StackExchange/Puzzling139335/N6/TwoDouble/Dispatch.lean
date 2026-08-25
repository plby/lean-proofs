import StackExchange.Puzzling139335.N6.TwoDouble.Normalization
import StackExchange.Puzzling139335.N6.TwoDouble.HorizontalNormalization
import StackExchange.Puzzling139335.N6.TwoDouble.HorizontalTypes
import StackExchange.Puzzling139335.N6.TwoDouble.HorizontalAcute
import StackExchange.Puzzling139335.N6.TwoDouble.MixedCornerGeometry
import StackExchange.Puzzling139335.N6.TwoDouble.Adjacent
import StackExchange.Puzzling139335.HalfTurnPair

/-!
# Exhaustive exclusion of two double corners

The repeated full unit pair is normalized by an actual common square
symmetry and a permutation of the pieces. Its remaining maps are the
horizontal reflection, the other diagonal reflection, and the central
half-turn. The horizontal case is split by the actual intrinsic types of
the two remaining pieces; the three-cornered alternative was excluded
during the owner normalization.
-/

open Set

namespace Puzzling139335.N6.TwoDouble

/-- The horizontal full-pair configuration is impossible, including both
orders of the remaining two owners and all of their intrinsic types. -/
theorem normalized_horizontal_impossible (d : SquareDissection)
    (hc : d.HasProtectedCenter) (hN : d.cornerIncidenceCount = 6)
    (hBL : corner 0 ∈ d.piece 0) (hBR : corner 1 ∈ d.piece 0)
    (hcount : d.cornerTileCount 0 = 1)
    (hH : ReflectionSeparation.horizontal '' d.piece 0 = d.piece 1) : False := by
  obtain ⟨D, hcD, hND, hUD, hBLD, hBRD, _, hHD, hHowner, hGowner⟩ :=
    exists_horizontal_ordered_owners_of_protected d hc hN hBL hBR hcount hH
  rcases horizontal_singleton_type_cases D hND hUD hBLD hBRD hHD hHowner hGowner with
    htype | htype | htype
  · exact HorizontalAcute.normalized_impossible D hcD hND hBLD hBRD hHD hHowner hGowner
      (Or.inl htype)
  · exact HorizontalAcute.normalized_impossible D hcD hND hBLD hBRD hHD hHowner hGowner
      (Or.inr htype)
  · exact MixedCornerGeometry.no_normalized_mixed_same_intrinsic D hcD hND
      hBLD hBRD hHD hHowner hGowner htype

/-- The complete two-double-corner case, with no independent intrinsic
type, local angle, placement, or boundary-regularity premise. -/
theorem two_double_corner_impossible (d : SquareDissection)
    (hc : d.HasProtectedCenter) (hN : d.cornerIncidenceCount = 6)
    (hdouble : HasTwoDoubleCorners d) : False := by
  obtain ⟨D, hcD, hND, hUD, _, hBLD, hBRD, hcountD, hmaps⟩ :=
    exists_canonical_full_pair d hc hN hdouble
  rcases hmaps with hhorizontal | hadjacent | hhalfturn
  · exact normalized_horizontal_impossible D hcD hND hBLD hBRD hcountD hhorizontal
  · obtain ⟨hTL₂, hTL₃⟩ :=
      antidiagonal_remaining_owners D hcD hND hBLD hBRD hcountD hadjacent
    exact Adjacent.normalized_impossible D hcD hND hUD hBLD hBRD hadjacent hTL₂ hTL₃
  · exact D.not_hasProtectedCenter_of_halfTurn_pair
      (by decide : (0 : Fin 4) ≠ 1) hhalfturn hcD

theorem not_hasProtectedCenter_of_two_double_corners (d : SquareDissection)
    (hN : d.cornerIncidenceCount = 6) (hdouble : HasTwoDoubleCorners d) :
    ¬ d.HasProtectedCenter := fun hc => two_double_corner_impossible d hc hN hdouble

end Puzzling139335.N6.TwoDouble
