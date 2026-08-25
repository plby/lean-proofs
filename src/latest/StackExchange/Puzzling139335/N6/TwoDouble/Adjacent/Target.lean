import StackExchange.Puzzling139335.N6.TwoDouble.Adjacent.Types

/-!
# The actual singleton placement of the acute source corner

All membership, multiplicity, and corner-mapping conclusions are derived
from the normalized dissection. The witness is the chosen congruence
between the actual pieces.
-/

open Set

namespace Puzzling139335.N6.TwoDouble.Adjacent

theorem exists_acute_singleton (d : SquareDissection)
    (hc : d.HasProtectedCenter) (hN : d.cornerIncidenceCount = 6)
    (hU : d.usedCornerTypes.card ≤ 3)
    (hBL : corner 0 ∈ d.piece 0) (hBR : corner 1 ∈ d.piece 0)
    (hanti : ReflectionSeparation.antiDiagonal '' d.piece 0 = d.piece 1)
    (hTL2 : corner 3 ∈ d.piece 2) (hTL3 : corner 3 ∈ d.piece 3) :
    ∃ k l : Fin 4, k ≠ l ∧ corner 3 ∈ d.piece k ∧ corner 3 ∈ d.piece l ∧
      (∀ m, m ≠ k → m ≠ l → corner 3 ∉ d.piece m) ∧
      d.tileCornerCount k = 1 ∧ d.relativePlacement 0 k (corner 1) = corner 3 := by
  have hdata := normalized_corner_data d hc hN hBL hBR hanti hTL2 hTL3
  have hother : ∀ m, m ≠ (2 : Fin 4) → m ≠ 3 → corner 3 ∉ d.piece m := by
    intro m hm2 hm3 hm
    exact ((hdata.corner_three_iff m).mp hm).elim hm2 hm3
  rcases top_left_uses_bottom_right_type_of_corner_data d hc hU hdata with h | h
  · exact ⟨2, 3, by decide, hTL2, hTL3, hother, hdata.tile_count_two,
      d.relativePlacement_corner h.symm⟩
  · exact ⟨3, 2, by decide, hTL3, hTL2,
      fun m hm3 hm2 => hother m hm2 hm3, hdata.tile_count_three,
      d.relativePlacement_corner h.symm⟩

end Puzzling139335.N6.TwoDouble.Adjacent
