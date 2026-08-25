import StackExchange.Puzzling139335.N7.FullTypes
import StackExchange.Puzzling139335.N7.TwoTwoTwoOne.AdjacentRepeated

/-!
# The shared corner of the two repeated pairs in the `2221` pattern

The unique physical corner has the other endpoint as its intrinsic type,
so neither repeated pair contains that corner. Their actual square sides
are distinct and avoid this corner; consequently the sides share another
corner. The actual relative placement fixes this shared corner, giving
equality of the two intrinsic occurrences.
-/

namespace Puzzling139335.N7

private theorem distinct_sides_avoiding_corner_intersect :
    ∀ s t q : Fin 4, s ≠ t →
      ¬ (q = s ∨ q = s + 1) → ¬ (q = t ∨ q = t + 1) →
      ∃ j : Fin 4, (j = s ∨ j = s + 1) ∧ (j = t ∨ j = t + 1) := by
  decide

namespace PairConfiguration

open N8

noncomputable section

variable {d : SquareDissection}

/-- A uniquely owned square corner belongs to neither repeated-pair
piece when there is exactly one uniquely owned square corner. -/
theorem repeated_pieces_avoid_unique_corner (C : PairConfiguration d)
    (hc : d.HasProtectedCenter)
    (hU : (Finset.univ.filter fun j : Fin 4 => d.cornerTileCount j = 1).card = 1)
    {q : Fin 4} (hq : d.cornerTileCount q = 1) :
    corner q ∉ d.piece (C.double 0) ∧ corner q ∉ d.piece (C.double 1) := by
  classical
  have hfull := C.full_types_eq_otherEnd_of_unique_count_one hc hU
  have hnot (i : Fin 4)
      (hpair : intrinsicPair d i = {C.common, C.repeatedEnd}) :
      corner q ∉ d.piece i := by
    intro hqi
    have hvfull : d.intrinsicCorner i q ∈ N5.fullCornerTypes d :=
      (intrinsicCorner_mem_full_iff_count_one d hqi).mpr hq
    rw [hfull] at hvfull
    have hvother := Finset.mem_singleton.mp hvfull
    have hvmem : d.intrinsicCorner i q ∈ intrinsicPair d i :=
      (mem_intrinsicPair d i _).mpr ⟨q, hqi, rfl⟩
    rw [hpair] at hvmem
    rcases Finset.mem_insert.mp hvmem with hvcommon | hvrepeated
    · exact C.common_ne_otherEnd (hvcommon.symm.trans hvother)
    · exact C.repeatedEnd_ne_otherEnd
        ((Finset.mem_singleton.mp hvrepeated).symm.trans hvother)
  exact ⟨hnot (C.double 0) C.pair_zero, hnot (C.double 1) C.pair_one⟩

/-- The two repeated pieces occupy distinct actual square sides meeting
at a shared physical corner. -/
theorem exists_adjacent_repeated_sides (C : PairConfiguration d)
    (hc : d.HasProtectedCenter)
    (hU : (Finset.univ.filter fun j : Fin 4 => d.cornerTileCount j = 1).card = 1) :
    ∃ s t j : Fin 4, IsLocalSide d (C.double 0) s ∧
      IsLocalSide d (C.double 1) t ∧ s ≠ t ∧
      corner j ∈ d.piece (C.double 0) ∧ corner j ∈ d.piece (C.double 1) := by
  obtain ⟨s, hs⟩ := exists_local_side_of_count_two d hc (C.double 0) (C.double_count 0)
  obtain ⟨t, ht⟩ := exists_local_side_of_count_two d hc (C.double 1) (C.double_count 1)
  have h01 := C.double_injective.ne (by decide : (0 : Fin 3) ≠ 1)
  have hpair := C.pair_zero.trans C.pair_one.symm
  have hst := local_sides_ne_of_intrinsicPair_eq d h01 hs ht hpair
  obtain ⟨q, hq⟩ := exists_count_one_corner d hc C.incidence_count
  obtain ⟨hq0, hq1⟩ := C.repeated_pieces_avoid_unique_corner hc hU hq
  have hqs : ¬ (q = s ∨ q = s + 1) := fun h => hq0 ((hs q).mpr h)
  have hqt : ¬ (q = t ∨ q = t + 1) := fun h => hq1 ((ht q).mpr h)
  obtain ⟨j, hjs, hjt⟩ := distinct_sides_avoiding_corner_intersect s t q hst hqs hqt
  exact ⟨s, t, j, hs, ht, hst, (hs j).mpr hjs, (ht j).mpr hjt⟩

/-- The two repeated pieces share an actual square corner. -/
theorem exists_shared_repeated_corner (C : PairConfiguration d)
    (hc : d.HasProtectedCenter)
    (hU : (Finset.univ.filter fun j : Fin 4 => d.cornerTileCount j = 1).card = 1) :
    ∃ j : Fin 4, corner j ∈ d.piece (C.double 0) ∧
      corner j ∈ d.piece (C.double 1) := by
  obtain ⟨_, _, j, _, _, _, hj0, hj1⟩ := C.exists_adjacent_repeated_sides hc hU
  exact ⟨j, hj0, hj1⟩

/-- The shared square corner is an occurrence of the same intrinsic type
in both repeated pieces; this equality follows from their actual relative
placement, not from a prescribed matching of intrinsic endpoints. -/
theorem exists_shared_repeated_occurrence (C : PairConfiguration d)
    (hc : d.HasProtectedCenter)
    (hU : (Finset.univ.filter fun j : Fin 4 => d.cornerTileCount j = 1).card = 1) :
    ∃ j : Fin 4, corner j ∈ d.piece (C.double 0) ∧
      corner j ∈ d.piece (C.double 1) ∧
      d.intrinsicCorner (C.double 0) j = d.intrinsicCorner (C.double 1) j := by
  obtain ⟨s, t, j, hs, ht, hst, hj0, hj1⟩ := C.exists_adjacent_repeated_sides hc hU
  refine ⟨j, hj0, hj1, ?_⟩
  exact intrinsicCorner_eq_of_adjacent_repeated_pair d hc
    (C.double_injective.ne (by decide : (0 : Fin 3) ≠ 1)) hs ht hst hj0 hj1
    (C.pair_zero.trans C.pair_one.symm)

end

end PairConfiguration

end Puzzling139335.N7
