import StackExchange.Puzzling139335.N6.TwoDouble.NormalizedTypes

/-!
# The singleton types of a normalized horizontal outer pair

The two right corners are double, the left corners are unique, and the
three-type bound leaves at most two split types. Consequently either a
middle piece repeats the outer right-corner type, or the two middle pieces
repeat each other's type. These alternatives concern the actual chosen
intrinsic points.
-/

open Set

namespace Puzzling139335.N6.TwoDouble

theorem horizontal_singleton_type_cases (d : SquareDissection)
    (hN : d.cornerIncidenceCount = 6) (hU : d.usedCornerTypes.card ≤ 3)
    (hBL : corner 0 ∈ d.piece 0) (hBR : corner 1 ∈ d.piece 0)
    (hreflect : ReflectionSeparation.horizontal '' d.piece 0 = d.piece 1)
    (hH : corner 1 ∈ d.piece 2) (hG : corner 2 ∈ d.piece 3) :
    d.intrinsicCorner 2 1 = d.intrinsicCorner 0 1 ∨
      d.intrinsicCorner 3 2 = d.intrinsicCorner 0 1 ∨
      d.intrinsicCorner 2 1 = d.intrinsicCorner 3 2 := by
  classical
  have hcounts := normalized_corner_counts_of_distinct_owners d hN
    (by decide : (0 : Fin 4) ≠ 2) (by decide : (1 : Fin 4) ≠ 3)
    hBR (normalized_top_right d hBR hreflect) hH hG
  have hfull : 0 < (N5.fullCornerTypes d).card := by
    apply Finset.card_pos.mpr
    exact ⟨d.intrinsicCorner 0 0,
      (N5.mem_fullCornerTypes d).mpr ⟨0, 0, hBL, hcounts.1, rfl⟩⟩
  have hsplit : (N5.splitCornerTypes d).card ≤ 2 := by
    have hsum := Finset.card_union_of_disjoint (N5.full_split_disjoint d)
    rw [← N5.usedCornerTypes_eq_union d] at hsum
    omega
  have ha : d.intrinsicCorner 0 1 ∈ N5.splitCornerTypes d :=
    (N5.mem_splitCornerTypes d).mpr ⟨0, 1, hBR, by omega, rfl⟩
  have hx : d.intrinsicCorner 2 1 ∈ N5.splitCornerTypes d :=
    (N5.mem_splitCornerTypes d).mpr ⟨2, 1, hH, by omega, rfl⟩
  have hy : d.intrinsicCorner 3 2 ∈ N5.splitCornerTypes d :=
    (N5.mem_splitCornerTypes d).mpr ⟨3, 2, hG, by omega, rfl⟩
  by_contra hnot
  simp only [not_or] at hnot
  have hsub : ({d.intrinsicCorner 2 1, d.intrinsicCorner 3 2,
      d.intrinsicCorner 0 1} : Finset Plane) ⊆ N5.splitCornerTypes d := by
    intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact hx
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact hy
    have hpa := Finset.mem_singleton.mp hp
    exact hpa ▸ ha
  have hcard : ({d.intrinsicCorner 2 1, d.intrinsicCorner 3 2,
      d.intrinsicCorner 0 1} : Finset Plane).card = 3 :=
    Finset.card_triple_eq_three_iff.mpr ⟨hnot.2.2, hnot.1, hnot.2.1⟩
  have hle := Finset.card_le_card hsub
  rw [hcard] at hle
  omega

end Puzzling139335.N6.TwoDouble
