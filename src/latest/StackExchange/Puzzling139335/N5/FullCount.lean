import StackExchange.Puzzling139335.N5.TypeSets
import StackExchange.Puzzling139335.N5.Incidence

/-!
# Three uniquely owned square corners require two intrinsic types

The lower bound is independent of the total incidence count and can be
used in every branch having three uniquely owned physical corners.
-/

open Set

namespace Puzzling139335.N5

theorem two_le_fullCornerTypes_card_of_three_unique_corners (d : SquareDissection)
    (hc : d.HasProtectedCenter) (a b c : Fin 4)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : d.cornerTileCount a = 1) (hb : d.cornerTileCount b = 1)
    (hc' : d.cornerTileCount c = 1) : 2 ≤ (fullCornerTypes d).card := by
  classical
  by_contra hnot
  have hcard : (fullCornerTypes d).card ≤ 1 := by omega
  obtain ⟨i, hi, hiUnique⟩ := unique_owner_of_count_one d a ha
  obtain ⟨j, hj, _⟩ := unique_owner_of_count_one d b hb
  obtain ⟨k, hk, _⟩ := unique_owner_of_count_one d c hc'
  have hit : d.intrinsicCorner i a ∈ fullCornerTypes d :=
    (mem_fullCornerTypes d).mpr ⟨i, a, hi, ha, rfl⟩
  have hjt : d.intrinsicCorner j b ∈ fullCornerTypes d :=
    (mem_fullCornerTypes d).mpr ⟨j, b, hj, hb, rfl⟩
  have hkt : d.intrinsicCorner k c ∈ fullCornerTypes d :=
    (mem_fullCornerTypes d).mpr ⟨k, c, hk, hc', rfl⟩
  exact not_three_equal_unique_types d hc hab hac hbc
    (fun m hmi hm => hmi (hiUnique m hm))
    (Finset.card_le_one_iff.mp hcard hit hjt)
    (Finset.card_le_one_iff.mp hcard hit hkt)

/-- Five incidences leave three physical corners uniquely owned, so their
intrinsic full-corner types cannot collapse to a single point. -/
theorem two_le_fullCornerTypes_card_of_five (d : SquareDissection)
    (hc : d.HasProtectedCenter) (hN : d.cornerIncidenceCount = 5) :
    2 ≤ (fullCornerTypes d).card := by
  obtain ⟨s, _, hother⟩ := exists_split_corner d hN
  have h₁ : s + 1 ≠ s := by fin_cases s <;> decide
  have h₂ : s + 2 ≠ s := by fin_cases s <;> decide
  have h₃ : s + 3 ≠ s := by fin_cases s <;> decide
  have h₁₂ : s + 1 ≠ s + 2 := by fin_cases s <;> decide
  have h₁₃ : s + 1 ≠ s + 3 := by fin_cases s <;> decide
  have h₂₃ : s + 2 ≠ s + 3 := by fin_cases s <;> decide
  exact two_le_fullCornerTypes_card_of_three_unique_corners d hc
    (s + 1) (s + 2) (s + 3) h₁₂ h₁₃ h₂₃
    (hother (s + 1) h₁) (hother (s + 2) h₂) (hother (s + 3) h₃)

theorem splitCornerTypes_nonempty_of_five (d : SquareDissection)
    (hN : d.cornerIncidenceCount = 5) : (splitCornerTypes d).Nonempty := by
  obtain ⟨s, hs, _⟩ := exists_split_corner d hN
  obtain ⟨i, hi⟩ := d.exists_piece_mem (corner_mem_unitSquare s)
  exact ⟨d.intrinsicCorner i s,
    (mem_splitCornerTypes d).mpr ⟨i, s, hi, by omega, rfl⟩⟩

end Puzzling139335.N5
