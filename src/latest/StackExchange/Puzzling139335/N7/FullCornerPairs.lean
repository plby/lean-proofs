import StackExchange.Puzzling139335.N7.Incidence
import StackExchange.Puzzling139335.N5.TypeSets
import StackExchange.Puzzling139335.N5.FullType
import StackExchange.Puzzling139335.UnitPairs

/-!
# Unsplit intrinsic corners restrict the used unit pairs

A full square-corner type has only one intrinsic unit-side partner.  Thus
three different pairs among three types are impossible as soon as one of
the types is used at an unsplit corner.  Seven incidences always provide
such a corner; the proof uses no polygonal angle argument.
-/

open Set

namespace Puzzling139335.N7

open UnitPairs

theorem isFullSquareCorner_of_mem_fullCornerTypes (d : SquareDissection)
    {v : Plane} (hv : v ∈ N5.fullCornerTypes d) :
    IsFullSquareCorner (d.piece 0) v := by
  obtain ⟨i, j, hj, hcount, htype⟩ := (N5.mem_fullCornerTypes d).mp hv
  rw [← htype]
  exact N5.isFullSquareCorner_of_unique_corner d i j
    (d.unique_corner_owner_of_count_one hcount hj)

theorem fullCornerTypes_nonempty (d : SquareDissection)
    (hc : d.HasProtectedCenter) (hN : d.cornerIncidenceCount = 7) :
    (N5.fullCornerTypes d).Nonempty := by
  obtain ⟨j, hj⟩ := exists_count_one_corner d hc hN
  obtain ⟨i, hi⟩ := d.exists_piece_mem (corner_mem_unitSquare j)
  exact ⟨d.intrinsicCorner i j, (N5.mem_fullCornerTypes d).mpr ⟨i, j, hi, hj, rfl⟩⟩

/-- A type with two distinct actual unit-side partners cannot be full. -/
theorem not_fullCornerType_of_two_partners (d : SquareDissection)
    (hc : d.HasProtectedCenter) {a b r : Plane}
    (hab : IsUnitSidePair (d.piece 0) a b)
    (har : IsUnitSidePair (d.piece 0) a r) (hbr : b ≠ r) :
    a ∉ N5.fullCornerTypes d := by
  intro ha
  exact hbr (unit_partners_eq_of_protected_center d hc 0
    (isFullSquareCorner_of_mem_fullCornerTypes d ha) hab har)

/-- All three pairs among three distinct types cannot be used when one
of those actual types is a full square corner. -/
theorem no_three_unitSidePairs_with_full_type (d : SquareDissection)
    (hc : d.HasProtectedCenter) {a b r v : Plane}
    (hab : a ≠ b) (har : a ≠ r) (hbr : b ≠ r)
    (hpab : IsUnitSidePair (d.piece 0) a b)
    (hpbr : IsUnitSidePair (d.piece 0) b r)
    (hpra : IsUnitSidePair (d.piece 0) r a)
    (hv : v ∈ N5.fullCornerTypes d) (hvtypes : v = a ∨ v = b ∨ v = r) : False := by
  rcases hvtypes with rfl | rfl | rfl
  · exact not_fullCornerType_of_two_partners d hc hpab hpra.symm hbr hv
  · exact not_fullCornerType_of_two_partners d hc hpab.symm hpbr har hv
  · exact not_fullCornerType_of_two_partners d hc hpra hpbr.symm hab hv

/-- In the seven-incidence case, using all three unit pairs of the three
used types is impossible. -/
theorem no_three_unitSidePairs_of_usedTypes (d : SquareDissection)
    (hc : d.HasProtectedCenter) (hN : d.cornerIncidenceCount = 7)
    {a b r : Plane} (hab : a ≠ b) (har : a ≠ r) (hbr : b ≠ r)
    (htypes : d.usedCornerTypes = {a, b, r})
    (hpab : IsUnitSidePair (d.piece 0) a b)
    (hpbr : IsUnitSidePair (d.piece 0) b r)
    (hpra : IsUnitSidePair (d.piece 0) r a) : False := by
  classical
  obtain ⟨v, hv⟩ := fullCornerTypes_nonempty d hc hN
  have hvused := N5.fullCornerTypes_subset_used d hv
  rw [htypes] at hvused
  apply no_three_unitSidePairs_with_full_type d hc hab har hbr hpab hpbr hpra hv
  simpa only [Finset.mem_insert, Finset.mem_singleton] using hvused

end Puzzling139335.N7
