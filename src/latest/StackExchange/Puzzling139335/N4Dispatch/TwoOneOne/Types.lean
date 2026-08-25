import StackExchange.Puzzling139335.GeometricReduction

/-!
# The repeated singleton type in the `2110` case

A type shared by two pieces with four total incidences forces their corner
counts to agree. Thus neither singleton type is one of the double piece's
two types. The three-type bound then makes the two singleton types equal.
-/

open Set

namespace Puzzling139335.N4Dispatch.TwoOneOne

noncomputable section

/-- The singleton pieces in the normalized `2110` pattern use the same
intrinsic corner point. -/
theorem singleton_types_eq (d : SquareDissection) (hc : d.HasProtectedCenter)
    (hN : d.cornerIncidenceCount = 4)
    (hBL : corner 0 ∈ d.piece 0) (hBR : corner 1 ∈ d.piece 0)
    (hTR : corner 2 ∈ d.piece 1) (hTL : corner 3 ∈ d.piece 2)
    (h0 : d.tileCornerCount 0 = 2) (h1 : d.tileCornerCount 1 = 1)
    (h2 : d.tileCornerCount 2 = 1) :
    d.intrinsicCorner 1 2 = d.intrinsicCorner 2 3 := by
  classical
  have hdouble : d.intrinsicCorner 0 0 ≠ d.intrinsicCorner 0 1 := by
    intro h
    exact (by decide : (0 : Fin 4) ≠ 1) (d.intrinsicCorner_injective 0 h)
  have hne (i : Fin 4) (hi : d.tileCornerCount i = 1)
      (a b : Fin 4) (ha : corner a ∈ d.piece 0) :
      d.intrinsicCorner 0 a ≠ d.intrinsicCorner i b := by
    intro h
    have hcount := d.tileCornerCount_eq_of_four_incidences_repeated_type hN ha h
    omega
  have hBLTR := hne 1 h1 0 2 hBL
  have hBLTL := hne 2 h2 0 3 hBL
  have hBRTR := hne 1 h1 1 2 hBR
  have hBRTL := hne 2 h2 1 3 hBR
  by_contra hsingle
  have hfour :
      ({d.intrinsicCorner 0 0, d.intrinsicCorner 0 1,
        d.intrinsicCorner 1 2, d.intrinsicCorner 2 3} : Finset Plane).card = 4 := by
    simp [hdouble, hBLTR, hBLTL, hBRTR, hBRTL, hsingle]
  have hsubset :
      ({d.intrinsicCorner 0 0, d.intrinsicCorner 0 1,
        d.intrinsicCorner 1 2, d.intrinsicCorner 2 3} : Finset Plane) ⊆
        d.usedCornerTypes := by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · exact d.mem_usedCornerTypes.mpr ⟨0, 0, hBL, rfl⟩
    · exact d.mem_usedCornerTypes.mpr ⟨0, 1, hBR, rfl⟩
    · exact d.mem_usedCornerTypes.mpr ⟨1, 2, hTR, rfl⟩
    · exact d.mem_usedCornerTypes.mpr ⟨2, 3, hTL, rfl⟩
  have hle := (Finset.card_le_card hsubset).trans (d.usedCornerTypes_card_le_three hc)
  omega

/-- The repeated singleton point gives an actual symmetry of the square
between the two singleton placements. -/
theorem singleton_relativePlacement_preserves_square
    (d : SquareDissection) (hc : d.HasProtectedCenter)
    (hN : d.cornerIncidenceCount = 4)
    (hBL : corner 0 ∈ d.piece 0) (hBR : corner 1 ∈ d.piece 0)
    (hTR : corner 2 ∈ d.piece 1) (hTL : corner 3 ∈ d.piece 2)
    (h0 : d.tileCornerCount 0 = 2) (h1 : d.tileCornerCount 1 = 1)
    (h2 : d.tileCornerCount 2 = 1) :
    d.relativePlacement 1 2 '' unitSquare = unitSquare :=
  d.relativePlacement_preserves_square_of_unique_corner
    (d.unique_corner_owner_of_four_incidences hN hTR)
    (singleton_types_eq d hc hN hBL hBR hTR hTL h0 h1 h2)

end

end Puzzling139335.N4Dispatch.TwoOneOne
