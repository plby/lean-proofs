import StackExchange.Puzzling139335.N6.TwoDouble.SingleSplit
import StackExchange.Puzzling139335.ReflectionSeparation

/-!
# Intrinsic endpoint matching in the normalized three-cornered-piece case

The lower and upper pieces own the two horizontal sides, and a third
piece owns the right side. Six incidences force the left corners to be
unique and the right corners to be double. With at most three intrinsic
types, the third piece must use the lower piece's right-corner type.
-/

open Set
open scoped BigOperators

namespace Puzzling139335.N6.TwoDouble

noncomputable section

private theorem two_le_count_of_two_owners (d : SquareDissection) {i j a : Fin 4}
    (hij : i ≠ j) (hi : corner a ∈ d.piece i) (hj : corner a ∈ d.piece j) :
    2 ≤ d.cornerTileCount a := by
  classical
  have hsub : ({i, j} : Finset (Fin 4)) ⊆
      Finset.univ.filter fun k => corner a ∈ d.piece k := by
    intro k hk
    rcases Finset.mem_insert.mp hk with rfl | hk
    · simp [hi]
    · have hkj := Finset.mem_singleton.mp hk
      subst k
      simp [hj]
  have hle := Finset.card_le_card hsub
  change 2 ≤ (Finset.univ.filter fun k => corner a ∈ d.piece k).card
  simpa only [Finset.card_pair hij] using hle

theorem normalized_corner_counts_of_distinct_owners (d : SquareDissection)
    (hN : d.cornerIncidenceCount = 6) {i j : Fin 4} (h0i : (0 : Fin 4) ≠ i)
    (h1j : (1 : Fin 4) ≠ j) (hBR : corner 1 ∈ d.piece 0)
    (hTR : corner 2 ∈ d.piece 1) (hBR' : corner 1 ∈ d.piece i)
    (hTR' : corner 2 ∈ d.piece j) :
    d.cornerTileCount 0 = 1 ∧ d.cornerTileCount 1 = 2 ∧
      d.cornerTileCount 2 = 2 ∧ d.cornerTileCount 3 = 1 := by
  have h1 := two_le_count_of_two_owners d h0i hBR hBR'
  have h2 := two_le_count_of_two_owners d h1j hTR hTR'
  have h0 := d.cornerTileCount_pos 0
  have h3 := d.cornerTileCount_pos 3
  have hsum : (∑ j, d.cornerTileCount j) = 6 :=
    d.cornerIncidenceCount_eq_sum_cornerTileCount.symm.trans hN
  rw [CornerCounting.sum_fin_four] at hsum
  omega

theorem normalized_corner_counts (d : SquareDissection)
    (hN : d.cornerIncidenceCount = 6) (hBR : corner 1 ∈ d.piece 0)
    (hTR : corner 2 ∈ d.piece 1) (hBR' : corner 1 ∈ d.piece 2)
    (hTR' : corner 2 ∈ d.piece 2) :
    d.cornerTileCount 0 = 1 ∧ d.cornerTileCount 1 = 2 ∧
      d.cornerTileCount 2 = 2 ∧ d.cornerTileCount 3 = 1 :=
  normalized_corner_counts_of_distinct_owners d hN (by decide) (by decide) hBR hTR hBR' hTR'

theorem normalized_third_cornerSet (d : SquareDissection) (hc : d.HasProtectedCenter)
    (hBR : corner 1 ∈ d.piece 2) (hTR : corner 2 ∈ d.piece 2) :
    N8.cornerSet d 2 = {1, 2} := by
  classical
  have hsub : ({1, 2} : Finset (Fin 4)) ⊆ N8.cornerSet d 2 := by
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact (N8.mem_cornerSet d 2 1).mpr hBR
    · have hj2 := Finset.mem_singleton.mp hj
      subst j
      exact (N8.mem_cornerSet d 2 2).mpr hTR
  apply Eq.symm
  apply Finset.eq_of_subset_of_card_le hsub
  rw [N8.cornerSet_card]
  simpa using d.tileCornerCount_le_two hc 2

theorem normalized_top_right (d : SquareDissection) (hBR : corner 1 ∈ d.piece 0)
    (hreflect : ReflectionSeparation.horizontal '' d.piece 0 = d.piece 1) :
    corner 2 ∈ d.piece 1 := by
  rw [← hreflect]
  refine ⟨corner 1, hBR, ?_⟩
  ext k
  fin_cases k <;> norm_num [corner, Fin.ext_iff]

/-- The full left-corner type cannot occur in the right-side piece. -/
theorem normalized_full_type_omitted (d : SquareDissection) (hc : d.HasProtectedCenter)
    (hN : d.cornerIncidenceCount = 6) (hBL : corner 0 ∈ d.piece 0)
    (hBR : corner 1 ∈ d.piece 0)
    (hreflect : ReflectionSeparation.horizontal '' d.piece 0 = d.piece 1)
    (hBR' : corner 1 ∈ d.piece 2) (hTR' : corner 2 ∈ d.piece 2) :
    d.intrinsicCorner 0 0 ∉ N8.intrinsicPair d 2 := by
  have hcounts := normalized_corner_counts d hN hBR
    (normalized_top_right d hBR hreflect) hBR' hTR'
  have hfull : d.intrinsicCorner 0 0 ∈ N5.fullCornerTypes d :=
    (N5.mem_fullCornerTypes d).mpr ⟨0, 0, hBL, hcounts.1, rfl⟩
  intro hmem
  obtain ⟨j, hj, htype⟩ := (N8.mem_intrinsicPair d 2 _).mp hmem
  have hjright : j = 1 ∨ j = 2 := by
    have hjc := (N8.mem_cornerSet d 2 j).mpr hj
    rw [normalized_third_cornerSet d hc hBR' hTR'] at hjc
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hjc
  have hcount : 1 < d.cornerTileCount j := by
    rcases hjright with rfl | rfl <;> omega
  have hsplit : d.intrinsicCorner 0 0 ∈ N5.splitCornerTypes d :=
    (N5.mem_splitCornerTypes d).mpr ⟨2, j, hj, hcount, htype⟩
  exact Finset.disjoint_left.mp (N5.full_split_disjoint d) hfull hsplit

/-- The three-type bound forces the lower piece's right-corner type to
occur at one of the third piece's two actual right-side corners. -/
theorem normalized_right_type_occurs (d : SquareDissection) (hc : d.HasProtectedCenter)
    (hN : d.cornerIncidenceCount = 6) (hU : d.usedCornerTypes.card ≤ 3)
    (hBL : corner 0 ∈ d.piece 0) (hBR : corner 1 ∈ d.piece 0)
    (hreflect : ReflectionSeparation.horizontal '' d.piece 0 = d.piece 1)
    (hBR' : corner 1 ∈ d.piece 2) (hTR' : corner 2 ∈ d.piece 2) :
    d.intrinsicCorner 0 1 ∈ N8.intrinsicPair d 2 := by
  classical
  have hrU : d.intrinsicCorner 0 0 ∈ d.usedCornerTypes :=
    d.mem_usedCornerTypes.mpr ⟨0, 0, hBL, rfl⟩
  have haU : d.intrinsicCorner 0 1 ∈ d.usedCornerTypes :=
    d.mem_usedCornerTypes.mpr ⟨0, 1, hBR, rfl⟩
  have har : d.intrinsicCorner 0 1 ≠ d.intrinsicCorner 0 0 :=
    (d.intrinsicCorner_injective 0).ne (by decide : (1 : Fin 4) ≠ 0)
  have hnot := normalized_full_type_omitted d hc hN hBL hBR hreflect hBR' hTR'
  have hsub : N8.intrinsicPair d 2 ⊆ d.usedCornerTypes.erase (d.intrinsicCorner 0 0) := by
    intro p hp
    refine Finset.mem_erase.mpr ⟨?_, N8.intrinsicPair_subset_usedCornerTypes d 2 hp⟩
    intro hpr
    exact hnot (hpr ▸ hp)
  have hcard : (N8.intrinsicPair d 2).card = 2 := by
    rw [N8.intrinsicPair_card, ← N8.cornerSet_card,
      normalized_third_cornerSet d hc hBR' hTR']
    decide
  have hbound : (d.usedCornerTypes.erase (d.intrinsicCorner 0 0)).card ≤ 2 := by
    have := Finset.card_erase_add_one hrU
    omega
  have heq := Finset.eq_of_subset_of_card_le hsub (by omega)
  rw [heq]
  exact Finset.mem_erase.mpr ⟨har, haU⟩

theorem normalized_relative_corner_image (d : SquareDissection) (hc : d.HasProtectedCenter)
    (hN : d.cornerIncidenceCount = 6) (hU : d.usedCornerTypes.card ≤ 3)
    (hBL : corner 0 ∈ d.piece 0) (hBR : corner 1 ∈ d.piece 0)
    (hreflect : ReflectionSeparation.horizontal '' d.piece 0 = d.piece 1)
    (hBR' : corner 1 ∈ d.piece 2) (hTR' : corner 2 ∈ d.piece 2) :
    d.relativePlacement 0 2 (corner 1) = corner 1 ∨
      d.relativePlacement 0 2 (corner 1) = corner 2 := by
  obtain ⟨j, hj, htype⟩ := (N8.mem_intrinsicPair d 2 _).mp
    (normalized_right_type_occurs d hc hN hU hBL hBR hreflect hBR' hTR')
  have hjright : j = 1 ∨ j = 2 := by
    have hjc := (N8.mem_cornerSet d 2 j).mpr hj
    rw [normalized_third_cornerSet d hc hBR' hTR'] at hjc
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hjc
  have hmap := d.relativePlacement_corner htype.symm
  rcases hjright with rfl | rfl
  · exact Or.inl hmap
  · exact Or.inr hmap

/-- The third piece supplies a second actual unit-side partner of the
source right corner, distinct from the lower piece's left corner. -/
theorem normalized_second_unit_partner (d : SquareDissection) (hc : d.HasProtectedCenter)
    (hN : d.cornerIncidenceCount = 6) (hU : d.usedCornerTypes.card ≤ 3)
    (hBL : corner 0 ∈ d.piece 0) (hBR : corner 1 ∈ d.piece 0)
    (hreflect : ReflectionSeparation.horizontal '' d.piece 0 = d.piece 1)
    (hBR' : corner 1 ∈ d.piece 2) (hTR' : corner 2 ∈ d.piece 2) :
    ∃ b : Plane, UnitPairs.IsUnitSidePair (d.piece 0) (corner 1) b ∧ b ≠ corner 0 := by
  classical
  have ha := normalized_right_type_occurs d hc hN hU hBL hBR hreflect hBR' hTR'
  have hcard : (N8.intrinsicPair d 2).card = 2 := by
    rw [N8.intrinsicPair_card, ← N8.cornerSet_card,
      normalized_third_cornerSet d hc hBR' hTR']
    decide
  obtain ⟨b, hab, hpair⟩ := exists_partner hcard ha
  have hbMem : b ∈ N8.intrinsicPair d 2 := by rw [hpair]; simp
  have hbr : b ≠ d.intrinsicCorner 0 0 := by
    intro hbr
    exact normalized_full_type_omitted d hc hN hBL hBR hreflect hBR' hTR' (hbr ▸ hbMem)
  have hunit := unitSidePair_of_pair_eq d hc hab hpair
  have himage := unitSidePair_image hunit (d.placement 0)
  rw [d.placement_image, d.placement_intrinsicCorner] at himage
  refine ⟨d.placement 0 b, himage, ?_⟩
  intro heq
  apply hbr
  apply (d.placement 0).injective
  simpa only [d.placement_intrinsicCorner] using heq

end

end Puzzling139335.N6.TwoDouble
