import StackExchange.Puzzling139335.N7.TwoTwoTwoOne.Supports
import StackExchange.Puzzling139335.N7.TwoTwoTwoOne.Incidence

/-!
# The singleton piece in the `2221` branch

Once the repeated pair meets itself at a common-type corner, the singleton
must use that common type too.  Otherwise three occurrences of the other
endpoint occupy just two remaining square corners, forcing a forbidden
same-type double corner.  With the common type in every piece, its supporting
cone excludes the center from every piece.
-/

open Set

namespace Puzzling139335.N7.TwoTwoTwoOne

variable {d : SquareDissection}

/-- Every actual occurrence of a nonfull type has multiplicity two in
the one-unique-corner branch. -/
theorem nonfull_corner_count_two (C : PairConfiguration d)
    (hc : d.HasProtectedCenter)
    (hU : (Finset.univ.filter fun j : Fin 4 => d.cornerTileCount j = 1).card = 1)
    {i j : Fin 4} (hi : corner j ∈ d.piece i)
    (hnot : d.intrinsicCorner i j ∉ N5.fullCornerTypes d) :
    d.cornerTileCount j = 2 := by
  have hne : d.cornerTileCount j ≠ 1 :=
    fun h => hnot ((intrinsicCorner_mem_full_iff_count_one d hi).mpr h)
  have hpos := d.cornerTileCount_pos j
  have hle := corner_count_le_two C hc hU j
  omega

end Puzzling139335.N7.TwoTwoTwoOne

namespace Puzzling139335.N7.PairConfiguration

open N8 AcuteCorner TwoTwoTwoOne

variable {d : SquareDissection}

/-- The singleton's only intrinsic corner is one of the two nonfull
types, and cannot be the full other endpoint. -/
theorem singleton_pair_cases_of_unique_count_one (C : PairConfiguration d)
    (hc : d.HasProtectedCenter)
    (hU : (Finset.univ.filter fun j : Fin 4 => d.cornerTileCount j = 1).card = 1) :
    intrinsicPair d C.singleton = {C.common} ∨
      intrinsicPair d C.singleton = {C.repeatedEnd} := by
  classical
  obtain ⟨v, hvset⟩ := Finset.card_eq_one.mp
    ((intrinsicPair_card d C.singleton).trans C.singleton_count)
  have hv : v ∈ intrinsicPair d C.singleton := by rw [hvset]; simp
  have hused := intrinsicPair_subset_usedCornerTypes d C.singleton hv
  rw [C.types] at hused
  simp only [Finset.mem_insert, Finset.mem_singleton] at hused
  rcases hused with hva | hvb | hvr
  · exact Or.inl (hva ▸ hvset)
  · exact Or.inr (hvb ▸ hvset)
  · exfalso
    apply C.singleton_type_not_full hv
    rw [C.full_types_eq_otherEnd_of_unique_count_one hc hU, hvr]
    simp

/-- If the two repeated pieces meet at their common-type corner, the
singleton cannot use the repeated endpoint.  This uses only actual corner
occurrences and the already proved two-corner support obstruction. -/
theorem no_singleton_repeatedEnd_of_common_double_corner (C : PairConfiguration d)
    (hc : d.HasProtectedCenter)
    (hU : (Finset.univ.filter fun j : Fin 4 => d.cornerTileCount j = 1).card = 1)
    {j : Fin 4}
    (hi0 : corner j ∈ d.piece (C.double 0))
    (hi1 : corner j ∈ d.piece (C.double 1))
    (h0type : d.intrinsicCorner (C.double 0) j = C.common)
    (h1type : d.intrinsicCorner (C.double 1) j = C.common)
    (hsingle : intrinsicPair d C.singleton = {C.repeatedEnd}) : False := by
  classical
  have h01 := C.double_injective.ne (by decide : (0 : Fin 3) ≠ 1)
  have hother := other_owners_excluded_of_count_le_two d h01 hi0 hi1
    (corner_count_le_two C hc hU j)
  obtain ⟨q, hq⟩ := exists_count_one_corner d hc C.incidence_count
  have hjq : j ≠ q := by
    intro h
    exact C.common_not_full hc ((N5.mem_fullCornerTypes d).mpr
      ⟨C.double 0, j, hi0, h.symm ▸ hq, h0type⟩)
  obtain ⟨b0, hb0, ht0⟩ := (mem_intrinsicPair d (C.double 0) C.repeatedEnd).mp
    (by rw [C.pair_zero]; simp)
  obtain ⟨b1, hb1, ht1⟩ := (mem_intrinsicPair d (C.double 1) C.repeatedEnd).mp
    (by rw [C.pair_one]; simp)
  obtain ⟨bs, hbs, hts⟩ := (mem_intrinsicPair d C.singleton C.repeatedEnd).mp
    (by rw [hsingle]; simp)
  have havoid {i x : Fin 4} (hx : corner x ∈ d.piece i)
      (htx : d.intrinsicCorner i x = C.repeatedEnd) : x ≠ q := by
    intro h
    apply C.repeatedEnd_not_full_of_unique_count_one hc hU
    exact (N5.mem_fullCornerTypes d).mpr ⟨i, x, hx, h.symm ▸ hq, htx⟩
  have h0j : b0 ≠ j := by
    intro h
    exact C.common_ne_repeatedEnd (h0type.symm.trans (h ▸ ht0))
  have h1j : b1 ≠ j := by
    intro h
    exact C.common_ne_repeatedEnd (h1type.symm.trans (h ▸ ht1))
  have hsj : bs ≠ j := by
    intro h
    exact hother C.singleton (C.double_ne_singleton 0).symm
      (C.double_ne_singleton 1).symm (h ▸ hbs)
  rcases three_avoiding_two_repeat q j b0 b1 bs hjq.symm
      (havoid hb0 ht0) h0j (havoid hb1 ht1) h1j (havoid hbs hts) hsj with h | h | h
  · subst b1
    exact C.no_repeatedEnd_double_corner hc h01 hb0 hb1
      (other_owners_excluded_of_count_le_two d h01 hb0 hb1
        (corner_count_le_two C hc hU b0)) ht0 ht1
  · subst bs
    exact C.no_repeatedEnd_double_corner hc (C.double_ne_singleton 0) hb0 hbs
      (other_owners_excluded_of_count_le_two d (C.double_ne_singleton 0) hb0 hbs
        (corner_count_le_two C hc hU b0)) ht0 hts
  · subst bs
    exact C.no_repeatedEnd_double_corner hc (C.double_ne_singleton 1) hb1 hbs
      (other_owners_excluded_of_count_le_two d (C.double_ne_singleton 1) hb1 hbs
        (corner_count_le_two C hc hU b1)) ht1 hts

/-- If every actual piece uses the common type and that type has a
forty-five-degree support, no piece can contain the square center. -/
theorem all_common_corners_exclude_center (C : PairConfiguration d)
    (hc : d.HasProtectedCenter)
    (hU : (Finset.univ.filter fun j : Fin 4 => d.cornerTileCount j = 1).card = 1)
    (hsingle : intrinsicPair d C.singleton = {C.common})
    (hsupport : Supports45 (d.piece 0) C.common) : False := by
  classical
  have hmem (i : Fin 4) : C.common ∈ intrinsicPair d i := by
    rcases C.exhaustive i with rfl | rfl | rfl | rfl
    · rw [C.pair_zero]
      simp
    · rw [C.pair_one]
      simp
    · rw [C.pair_two]
      simp
    · rw [hsingle]
      simp
  obtain ⟨i, hicenter⟩ := hc
  have hc : d.HasProtectedCenter := ⟨i, hicenter⟩
  obtain ⟨j, hj, htype⟩ := (mem_intrinsicPair d i C.common).mp (hmem i)
  have hnotfull : d.intrinsicCorner i j ∉ N5.fullCornerTypes d := by
    simpa only [htype] using C.common_not_full hc
  have hcount := nonfull_corner_count_two C hc hU hj hnotfull
  obtain ⟨k, hki, hk, hother⟩ := exists_other_owner_of_count_two d hj hcount
  exact center_excluded_of_supported_type d hki.symm hj hk hother htype hsupport hicenter

/-- A common-type double corner of the repeated pieces excludes the
entire one-unique-corner configuration. -/
theorem no_common_double_corner_of_unique_count_one (C : PairConfiguration d)
    (hc : d.HasProtectedCenter)
    (hU : (Finset.univ.filter fun j : Fin 4 => d.cornerTileCount j = 1).card = 1)
    {j : Fin 4}
    (hi0 : corner j ∈ d.piece (C.double 0))
    (hi1 : corner j ∈ d.piece (C.double 1))
    (h0type : d.intrinsicCorner (C.double 0) j = C.common)
    (h1type : d.intrinsicCorner (C.double 1) j = C.common) : False := by
  have h01 := C.double_injective.ne (by decide : (0 : Fin 3) ≠ 1)
  have hother := other_owners_excluded_of_count_le_two d h01 hi0 hi1
    (corner_count_le_two C hc hU j)
  have hsupport : Supports45 (d.piece 0) C.common := by
    simpa only [h0type] using d.same_intrinsic_double_corner_prototype_support
      h01 hi0 hi1 hother (h0type.trans h1type.symm)
  rcases C.singleton_pair_cases_of_unique_count_one hc hU with hs | hs
  · exact C.all_common_corners_exclude_center hc hU hs hsupport
  · exact C.no_singleton_repeatedEnd_of_common_double_corner hc hU hi0 hi1 h0type h1type hs

/-- Equal intrinsic preimages at a shared corner of the two repeated
pieces are impossible in the one-unique-corner branch. -/
theorem no_same_type_repeated_shared_corner (C : PairConfiguration d)
    (hc : d.HasProtectedCenter)
    (hU : (Finset.univ.filter fun j : Fin 4 => d.cornerTileCount j = 1).card = 1)
    {j : Fin 4}
    (hi0 : corner j ∈ d.piece (C.double 0))
    (hi1 : corner j ∈ d.piece (C.double 1))
    (htype : d.intrinsicCorner (C.double 0) j = d.intrinsicCorner (C.double 1) j) :
    False := by
  classical
  have hpair : d.intrinsicCorner (C.double 0) j ∈ intrinsicPair d (C.double 0) :=
    (mem_intrinsicPair d (C.double 0) _).mpr ⟨j, hi0, rfl⟩
  rw [C.pair_zero] at hpair
  rcases Finset.mem_insert.mp hpair with ha | hb
  · exact C.no_common_double_corner_of_unique_count_one hc hU hi0 hi1
      ha (htype.symm.trans ha)
  · have hb := Finset.mem_singleton.mp hb
    have h01 := C.double_injective.ne (by decide : (0 : Fin 3) ≠ 1)
    exact C.no_repeatedEnd_double_corner hc h01 hi0 hi1
      (other_owners_excluded_of_count_le_two d h01 hi0 hi1
        (corner_count_le_two C hc hU j)) hb (htype.symm.trans hb)

end Puzzling139335.N7.PairConfiguration
