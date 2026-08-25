import StackExchange.Puzzling139335.N5.TypeReduction

/-!
# Repeated full types and tile degrees

Two full types suffice for all uniquely owned square corners.  If two
occurrences have corner counts different from a third occurrence, the
first two must represent the same intrinsic point: neither can represent
the third full type, because full-type placements preserve corner counts.
-/

namespace Puzzling139335.N5

theorem eq_of_mem_two_type_set {α : Type*} [DecidableEq α]
    {s : Finset α} {a b c : α} (hcard : s.card ≤ 2)
    (ha : a ∈ s) (hb : b ∈ s) (hc : c ∈ s)
    (hac : a ≠ c) (hbc : b ≠ c) : a = b := by
  by_contra hab
  have hthree : ({a, b, c} : Finset α).card = 3 := by
    simp [hab, hac, hbc]
  have hsub : ({a, b, c} : Finset α) ⊆ s := by
    simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
    exact ⟨ha, hb, hc⟩
  have hle := Finset.card_le_card hsub
  omega

theorem equal_full_types_of_count_ne_third (d : SquareDissection)
    (hcard : (fullCornerTypes d).card ≤ 2) {i j k a b c : Fin 4}
    (ha : d.intrinsicCorner i a ∈ fullCornerTypes d)
    (hb : d.intrinsicCorner j b ∈ fullCornerTypes d)
    (hc : d.intrinsicCorner k c ∈ fullCornerTypes d)
    (hik : d.tileCornerCount i ≠ d.tileCornerCount k)
    (hjk : d.tileCornerCount j ≠ d.tileCornerCount k) :
    d.intrinsicCorner i a = d.intrinsicCorner j b := by
  classical
  apply eq_of_mem_two_type_set hcard ha hb hc
  · intro htype
    exact hik (tileCornerCount_eq_of_full_type d ha htype)
  · intro htype
    exact hjk (tileCornerCount_eq_of_full_type d hb htype)

/-- In the `2210` branch, the two double-corner tiles use the same full
type away from the split corner; the singleton's full type is different. -/
theorem double_tiles_full_types_equal (d : SquareDissection)
    (hprotected : d.HasProtectedCenter) (hN : d.cornerIncidenceCount = 5)
    (htypes : d.usedCornerTypes.card ≤ 3) {i j k a b c : Fin 4}
    (hi : d.tileCornerCount i = 2) (hj : d.tileCornerCount j = 2)
    (hk : d.tileCornerCount k = 1)
    (ha : corner a ∈ d.piece i) (hb : corner b ∈ d.piece j)
    (hc : corner c ∈ d.piece k)
    (hca : d.cornerTileCount a = 1) (hcb : d.cornerTileCount b = 1)
    (hcc : d.cornerTileCount c = 1) :
    d.intrinsicCorner i a = d.intrinsicCorner j b := by
  apply equal_full_types_of_count_ne_third d
    (type_cardinalities_of_five d hprotected hN htypes).1.le
    ((mem_fullCornerTypes d).mpr ⟨i, a, ha, hca, rfl⟩)
    ((mem_fullCornerTypes d).mpr ⟨j, b, hb, hcb, rfl⟩)
    ((mem_fullCornerTypes d).mpr ⟨k, c, hc, hcc, rfl⟩)
  · omega
  · omega

end Puzzling139335.N5
