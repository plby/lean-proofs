import StackExchange.Puzzling139335.RectangularHull
import StackExchange.Puzzling139335.N4TypeCount

/-!
# The intrinsic-type bound in a putative counterexample

Equality in the four-corner support bound forces a rectangular hull, and
the full rectangular-hull theorem excludes it. Thus every putative
counterexample has at most three used intrinsic corner types.
-/

namespace Puzzling139335.SquareDissection

theorem not_hasProtectedCenter_of_four_usedCornerTypes (d : SquareDissection)
    (hfour : d.usedCornerTypes.card = 4) : ¬ d.HasProtectedCenter :=
  d.not_protectedCenter_of_rectangular_hull
    (d.hasRectangularHull_of_four_usedCornerTypes hfour)

/-- The strict intrinsic-type bound follows from the original dissection
hypotheses and the protected-center assumption, with no extra reduction premise. -/
theorem usedCornerTypes_card_le_three (d : SquareDissection)
    (hc : d.HasProtectedCenter) : d.usedCornerTypes.card ≤ 3 :=
  d.usedCornerTypes_card_le_three_of_not_rectangular (d.no_rectangular_hull hc 0)

theorem usedCornerTypes_card_eq_three_of_one_corner_per_piece
    (d : SquareDissection) (hc : d.HasProtectedCenter)
    (hN : d.cornerIncidenceCount = 4) (hcorners : ∀ i, ∃ j, corner j ∈ d.piece i) :
    d.usedCornerTypes.card = 3 :=
  le_antisymm (d.usedCornerTypes_card_le_three hc)
    (d.three_le_usedCornerTypes_card_of_four_incidences hc hN hcorners)

end Puzzling139335.SquareDissection
