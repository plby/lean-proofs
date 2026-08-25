import StackExchange.Puzzling139335.N6.TwoDouble.Adjacent.Geometry
import StackExchange.Puzzling139335.N6.TwoDouble.Adjacent.BottomSide
import StackExchange.Puzzling139335.N6.TwoDouble.Adjacent.Target
import StackExchange.Puzzling139335.N6.TwoDouble.UnitRay.Dissection
import StackExchange.Puzzling139335.N6.TwoDouble.RemainingOwners

/-!
# Adjacent full-corner copies in the six-incidence case

The actual anti-diagonal pair supplies a filled forty-five-degree corner.
Coverage and a Jordan height barrier give the full bottom side to its
source piece. The intrinsic corner count forces another copy of that
acute corner in a singleton at top left. Its transported unit ray either
creates a second corner or reaches the square center, both impossible.

Every incidence and segment used in the argument belongs to the actual
closed pieces; no convex-hull segment is promoted to a piece segment.
-/

open Set

namespace Puzzling139335.N6.TwoDouble.Adjacent

open ReflectionSeparation

/-- The normalized adjacent branch is impossible under the original
protected-center, incidence, and intrinsic-type assumptions. -/
theorem normalized_impossible (d : SquareDissection)
    (hc : d.HasProtectedCenter) (hN : d.cornerIncidenceCount = 6)
    (hU : d.usedCornerTypes.card ≤ 3)
    (hBL : corner 0 ∈ d.piece 0) (hBR : corner 1 ∈ d.piece 0)
    (hanti : antiDiagonal '' d.piece 0 = d.piece 1)
    (hTL2 : corner 3 ∈ d.piece 2) (hTL3 : corner 3 ∈ d.piece 3) : False := by
  have hdata := normalized_corner_data d hc hN hBL hBR hanti hTL2 hTL3
  have hBR1 := (reflected_corner_memberships d hBL hBR hanti).1
  have hbottom := bottom_side_subset d hc hBL hBR hanti hTL2 hTL3
  have hseg : segment ℝ (corner 1) (corner 0) ⊆ d.piece 0 := by
    rw [segment_symm]
    exact hbottom
  obtain ⟨k, l, hkl, hk, _, hother, hcount, hmap⟩ :=
    exists_acute_singleton d hc hN hU hBL hBR hanti hTL2 hTL3
  exact UnitRay.singleton_unitRay_from_repeated_corner_impossible d hc
    (by decide : (0 : Fin 4) ≠ 1) hBR hBR1 hdata.only_bottom_right
    antiDiagonal hanti antiDiagonal_bottom_right hkl hk hother
    (d.relativePlacement 0 k) (d.relativePlacement_image 0 k) hmap hcount hseg
    (Or.inr rfl)

/-- The two remaining top-left owners are also derived when the
bottom-left corner of the full pair is uniquely owned. -/
theorem antidiagonal_pair_impossible (d : SquareDissection)
    (hc : d.HasProtectedCenter) (hN : d.cornerIncidenceCount = 6)
    (hU : d.usedCornerTypes.card ≤ 3)
    (hBL : corner 0 ∈ d.piece 0) (hBR : corner 1 ∈ d.piece 0)
    (hBLcount : d.cornerTileCount 0 = 1)
    (hanti : antiDiagonal '' d.piece 0 = d.piece 1) : False := by
  obtain ⟨hTL2, hTL3⟩ := antidiagonal_remaining_owners d hc hN hBL hBR hBLcount hanti
  exact normalized_impossible d hc hN hU hBL hBR hanti hTL2 hTL3

end Puzzling139335.N6.TwoDouble.Adjacent
