import StackExchange.Puzzling139335.N6.TwoDouble.NormalizedTypes
import StackExchange.Puzzling139335.N6.TwoDouble.DiagonalData

/-!
# The normalized three-two-corner-piece branch is impossible

The endpoint matching, the multiplicities of the two right corners, the
actual diagonal sample, and the second unit-side partner are all derived
from the dissection. The normalized outer reflection is the only placement
identity assumed by this theorem.
-/

open Set

namespace Puzzling139335.N6.TwoDouble

/-- In a six-incidence dissection, a horizontally reflected outer pair
occupying the bottom and top sides leaves no room for a third congruent
piece occupying the right side, when there are at most three used types. -/
theorem normalized_three_cornered_impossible (d : SquareDissection)
    (hc : d.HasProtectedCenter) (hN : d.cornerIncidenceCount = 6)
    (hU : d.usedCornerTypes.card ≤ 3)
    (hBL : corner 0 ∈ d.piece 0) (hBR : corner 1 ∈ d.piece 0)
    (hreflect : ReflectionSeparation.horizontal '' d.piece 0 = d.piece 1)
    (hBR' : corner 1 ∈ d.piece 2) (hTR' : corner 2 ∈ d.piece 2) : False := by
  have hcounts := normalized_corner_counts d hN hBR
    (normalized_top_right d hBR hreflect) hBR' hTR'
  have hcorner := normalized_relative_corner_image d hc hN hU hBL hBR hreflect hBR' hTR'
  obtain ⟨hsupport, t, ht, hsample⟩ := right_corner_data_of_count_two d hBL hBR
    hreflect.symm hcounts.2.1 hcounts.2.2.1
    (d.relativePlacement 0 2) (d.relativePlacement_image 0 2) hcorner
  obtain ⟨b, hpair, hne⟩ :=
    normalized_second_unit_partner d hc hN hU hBL hBR hreflect hBR' hTR'
  have hhalf := (d.horizontal_pair_halves_of_bottom_left
    (by decide : (0 : Fin 4) ≠ 1) hreflect hBL).1
  exact diagonal_partner_lower_half_impossible (d.piece_subset 0) hBL
    (fun _ hp => hhalf hp) hsupport ht hsample hpair hne

end Puzzling139335.N6.TwoDouble
