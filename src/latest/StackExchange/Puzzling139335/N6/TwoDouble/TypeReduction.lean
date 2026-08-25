import StackExchange.Puzzling139335.N6.TwoDouble.FullPair

/-!
# Intrinsic type reduction at two double corners

There are four incidences at the split corners. If all use the same
intrinsic point, no piece can supply two of them, so every piece is
incident with a split corner. Otherwise the three-type bound leaves one
full type, and the actual repeated unit-pair reduction applies.
-/

open Set

namespace Puzzling139335.N6.TwoDouble

noncomputable section

/-- Under a one-type split hypothesis, the two split-corner owner sets
partition all four actual pieces. -/
theorem all_pieces_own_split_of_one_type (d : SquareDissection)
    {s t : Fin 4} (hst : s ≠ t) (hs : d.cornerTileCount s = 2)
    (ht : d.cornerTileCount t = 2) (hcard : (N5.splitCornerTypes d).card ≤ 1) :
    ∀ i : Fin 4, corner s ∈ d.piece i ∨ corner t ∈ d.piece i := by
  classical
  let S : Finset (Fin 4) := Finset.univ.filter fun i => corner s ∈ d.piece i
  let T : Finset (Fin 4) := Finset.univ.filter fun i => corner t ∈ d.piece i
  have hS : S.card = 2 := hs
  have hT : T.card = 2 := ht
  have hdis : Disjoint S T := by
    apply Finset.disjoint_left.mpr
    intro i hiS hiT
    have his : corner s ∈ d.piece i := (Finset.mem_filter.mp hiS).2
    have hit : corner t ∈ d.piece i := (Finset.mem_filter.mp hiT).2
    have hrs : d.intrinsicCorner i s ∈ N5.splitCornerTypes d :=
      (N5.mem_splitCornerTypes d).mpr ⟨i, s, his, by omega, rfl⟩
    have hrt : d.intrinsicCorner i t ∈ N5.splitCornerTypes d :=
      (N5.mem_splitCornerTypes d).mpr ⟨i, t, hit, by omega, rfl⟩
    exact hst (d.intrinsicCorner_injective i (Finset.card_le_one_iff.mp hcard hrs hrt))
  have hST : (S ∪ T).card = 4 := by
    rw [Finset.card_union_of_disjoint hdis, hS, hT]
  have hSTuniv : S ∪ T = Finset.univ :=
    Finset.eq_of_subset_of_card_le (Finset.subset_univ _) (by simp [hST])
  intro i
  have hi : i ∈ S ∪ T := by rw [hSTuniv]; exact Finset.mem_univ i
  simpa only [S, T, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] using hi

/-- At either double corner, the two owners use equal intrinsic points
when there is just one split type. -/
theorem intrinsic_eq_of_one_split_type (d : SquareDissection)
    (hcard : (N5.splitCornerTypes d).card ≤ 1) {s i j : Fin 4}
    (hs : d.cornerTileCount s = 2) (hi : corner s ∈ d.piece i)
    (hj : corner s ∈ d.piece j) :
    d.intrinsicCorner i s = d.intrinsicCorner j s := by
  classical
  exact Finset.card_le_one_iff.mp hcard
    ((N5.mem_splitCornerTypes d).mpr ⟨i, s, hi, by omega, rfl⟩)
    ((N5.mem_splitCornerTypes d).mpr ⟨j, s, hj, by omega, rfl⟩)

/-- If at least two split types are used, exactly one full type remains. -/
theorem one_full_type_of_two_split_types (d : SquareDissection)
    (hU : d.usedCornerTypes.card ≤ 3) (hD : HasTwoDoubleCorners d)
    (hsplit : 2 ≤ (N5.splitCornerTypes d).card) :
    (N5.fullCornerTypes d).card = 1 ∧ (N5.splitCornerTypes d).card = 2 ∧
      d.usedCornerTypes.card = 3 := by
  classical
  obtain ⟨a, _, _, ha, _⟩ := exists_two_unique_corners d hD
  obtain ⟨i, hi⟩ := d.incidence_covers a
  have hfull : 0 < (N5.fullCornerTypes d).card :=
    Finset.card_pos.mpr ⟨d.intrinsicCorner i a,
      (N5.mem_fullCornerTypes d).mpr ⟨i, a, hi, ha, rfl⟩⟩
  have hsum := Finset.card_union_of_disjoint (N5.full_split_disjoint d)
  rw [← N5.usedCornerTypes_eq_union d] at hsum
  omega

/-- The complete type reduction, stated as a disjunction of a repeated
split type and an actual pair of full-corner copies. -/
theorem single_split_type_or_full_pair (d : SquareDissection)
    (hc : d.HasProtectedCenter) (hN : d.cornerIncidenceCount = 6)
    (hU : d.usedCornerTypes.card ≤ 3) (hD : HasTwoDoubleCorners d) :
    (N5.splitCornerTypes d).card ≤ 1 ∨
      ∃ i j : Fin 4, i ≠ j ∧ ∃ r v : Plane, r ≠ v ∧
        UnitPairs.IsFullSquareCorner (d.piece 0) r ∧
        N8.intrinsicPair d i = {r, v} ∧ N8.intrinsicPair d j = {r, v} ∧
        d.relativePlacement i j '' unitSquare = unitSquare ∧
        squareCenter ∉ interior (d.piece i) ∧ squareCenter ∉ interior (d.piece j) := by
  by_cases hsplit : (N5.splitCornerTypes d).card ≤ 1
  · exact Or.inl hsplit
  · right
    have hcounts := one_full_type_of_two_split_types d hU hD (by omega)
    exact exists_full_pair_of_one_full_type d hc hN hU hD hcounts.1.le

end

end Puzzling139335.N6.TwoDouble
