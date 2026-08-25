import StackExchange.Puzzling139335.N7.TypeReduction
import StackExchange.Puzzling139335.N5.TypeReduction
import StackExchange.Puzzling139335.N7.FullTypes.Counting

/-!
# Full and split types in the seven-incidence configuration

The single-corner piece cannot use a full corner type: every used type also
occurs in a two-corner piece, and repeated full types preserve actual corner
counts.  The common endpoint of the two different pairs is also not full.
Thus only the two remaining endpoints can occur at uniquely owned corners.
-/

open Set
open scoped BigOperators

namespace Puzzling139335.N7.PairConfiguration

open N8

noncomputable section

variable {d : SquareDissection}

/-- Every used intrinsic type occurs in one of the three double-corner
pieces recorded by the configuration. -/
theorem used_type_occurs_in_double (C : PairConfiguration d) {v : Plane}
    (hv : v ∈ d.usedCornerTypes) :
    ∃ n : Fin 3, v ∈ intrinsicPair d (C.double n) := by
  classical
  rw [C.types] at hv
  rcases Finset.mem_insert.mp hv with hv | hv
  · refine ⟨0, ?_⟩
    rw [C.pair_zero, hv]
    simp
  · rcases Finset.mem_insert.mp hv with hv | hv
    · refine ⟨0, ?_⟩
      rw [C.pair_zero, hv]
      simp
    · refine ⟨2, ?_⟩
      rw [C.pair_two, Finset.mem_singleton.mp hv]
      simp

/-- An intrinsic type used by the single-corner piece cannot be full.
This follows from actual repeated-corner rigidity, independently of any
angle assignment. -/
theorem singleton_type_not_full (C : PairConfiguration d) {v : Plane}
    (hv : v ∈ intrinsicPair d C.singleton) : v ∉ N5.fullCornerTypes d := by
  intro hfull
  obtain ⟨j, hj, hjv⟩ := (mem_intrinsicPair d C.singleton v).mp hv
  obtain ⟨n, hvn⟩ := C.used_type_occurs_in_double
    (intrinsicPair_subset_usedCornerTypes d C.singleton hv)
  obtain ⟨k, hk, hkv⟩ := (mem_intrinsicPair d (C.double n) v).mp hvn
  have hfullj : d.intrinsicCorner C.singleton j ∈ N5.fullCornerTypes d := by
    simpa only [hjv] using hfull
  have heq := N5.tileCornerCount_eq_of_full_type d hfullj (hjv.trans hkv.symm)
  rw [C.singleton_count, C.double_count n] at heq
  omega

/-- No full type occurs at an actual corner of the single-corner piece. -/
theorem singleton_pair_disjoint_full (C : PairConfiguration d) :
    Disjoint (intrinsicPair d C.singleton) (N5.fullCornerTypes d) := by
  classical
  exact Finset.disjoint_left.mpr fun _ hv => C.singleton_type_not_full hv

/-- The one actual corner of the single-corner piece is necessarily shared
with another piece. -/
theorem singleton_corner_split (C : PairConfiguration d) {j : Fin 4}
    (hj : corner j ∈ d.piece C.singleton) : 1 < d.cornerTileCount j := by
  have hnot : d.cornerTileCount j ≠ 1 := by
    intro hcount
    exact C.singleton_type_not_full
      ((mem_intrinsicPair d C.singleton _).mpr ⟨j, hj, rfl⟩)
      ((N5.mem_fullCornerTypes d).mpr ⟨C.singleton, j, hj, hcount, rfl⟩)
  have hpos := d.cornerTileCount_pos j
  omega

/-- Every intrinsic type used by the single-corner piece belongs to the
actual split-type set. -/
theorem singleton_type_mem_split (C : PairConfiguration d) {v : Plane}
    (hv : v ∈ intrinsicPair d C.singleton) : v ∈ N5.splitCornerTypes d := by
  obtain ⟨j, hj, hjv⟩ := (mem_intrinsicPair d C.singleton v).mp hv
  exact (N5.mem_splitCornerTypes d).mpr
    ⟨C.singleton, j, hj, C.singleton_corner_split hj, hjv⟩

/-- The two noncommon endpoints are the only possible full corner types. -/
theorem full_types_subset_endpoints (C : PairConfiguration d)
    (hc : d.HasProtectedCenter) :
    N5.fullCornerTypes d ⊆ {C.repeatedEnd, C.otherEnd} := by
  classical
  intro v hv
  have hvused := N5.fullCornerTypes_subset_used d hv
  rw [C.types] at hvused
  rcases Finset.mem_insert.mp hvused with hva | hvbr
  · exact False.elim (C.common_not_full hc (hva ▸ hv))
  · exact hvbr

/-- The common type is an actual split type. -/
theorem common_mem_split (C : PairConfiguration d)
    (hc : d.HasProtectedCenter) : C.common ∈ N5.splitCornerTypes d := by
  classical
  have hused : C.common ∈ d.usedCornerTypes := by rw [C.types]; simp
  rw [N5.usedCornerTypes_eq_union] at hused
  exact (Finset.mem_union.mp hused).resolve_left (C.common_not_full hc)

/-- A sum over all four actual pieces can be evaluated in configuration
order, since the displayed pieces are distinct and exhaustive. -/
theorem sum_pieces (C : PairConfiguration d) (f : Fin 4 → ℕ) :
    (∑ i, f i) = f (C.double 0) + f (C.double 1) +
      f (C.double 2) + f C.singleton := by
  have huniv : (Finset.univ : Finset (Fin 4)) =
      {C.double 0, C.double 1, C.double 2, C.singleton} := by
    ext i
    simp only [Finset.mem_univ, true_iff, Finset.mem_insert, Finset.mem_singleton]
    exact C.exhaustive i
  rw [huniv]
  have h01 := C.double_injective.ne (by decide : (0 : Fin 3) ≠ 1)
  have h02 := C.double_injective.ne (by decide : (0 : Fin 3) ≠ 2)
  have h12 := C.double_injective.ne (by decide : (1 : Fin 3) ≠ 2)
  simp [h01, h02, h12, C.double_ne_singleton, add_assoc]

/-- The recorded actual corner counts themselves imply seven incidences. -/
theorem incidence_count (C : PairConfiguration d) : d.cornerIncidenceCount = 7 := by
  rw [d.cornerIncidenceCount_eq_sum_tileCornerCount, C.sum_pieces]
  simp [C.double_count, C.singleton_count]

/-- Counting uniquely owned physical corners by their actual intrinsic
occurrences gives multiplicity two for the repeated endpoint and one for
the other endpoint. -/
theorem unique_corner_count_formula (C : PairConfiguration d)
    (hc : d.HasProtectedCenter) :
    (Finset.univ.filter fun j : Fin 4 => d.cornerTileCount j = 1).card =
      (if C.repeatedEnd ∈ N5.fullCornerTypes d then 2 else 0) +
        (if C.otherEnd ∈ N5.fullCornerTypes d then 1 else 0) := by
  classical
  have hs : ((intrinsicPair d C.singleton).filter
      fun v => v ∈ N5.fullCornerTypes d) = ∅ :=
    Finset.filter_eq_empty_iff.mpr fun _ hv => C.singleton_type_not_full hv
  rw [unique_corner_count_eq_full_occurrences d, C.sum_pieces,
    C.pair_zero, C.pair_one, C.pair_two, hs]
  by_cases hb : C.repeatedEnd ∈ N5.fullCornerTypes d <;>
    by_cases hr : C.otherEnd ∈ N5.fullCornerTypes d <;>
      simp [Finset.filter_insert, Finset.filter_singleton, C.common_not_full hc, hb, hr]

/-- In the seven-incidence configuration, at most two physical corners
have a unique owner. -/
theorem unique_corner_count_le_two (C : PairConfiguration d)
    (hc : d.HasProtectedCenter) :
    (Finset.univ.filter fun j : Fin 4 => d.cornerTileCount j = 1).card ≤ 2 := by
  rcases corner_count_card_patterns d hc C.incidence_count with h | h <;> omega

/-- Both endpoints cannot be full: their actual occurrences would give
three uniquely owned physical corners. -/
theorem not_both_endpoints_full (C : PairConfiguration d)
    (hc : d.HasProtectedCenter) :
    ¬(C.repeatedEnd ∈ N5.fullCornerTypes d ∧ C.otherEnd ∈ N5.fullCornerTypes d) := by
  rintro ⟨hb, hr⟩
  have hcount := C.unique_corner_count_formula hc
  have hbound := C.unique_corner_count_le_two hc
  simp only [if_pos hb, if_pos hr] at hcount
  omega

/-- At least one of the two endpoints is full, since seven incidences
always leave a uniquely owned physical corner. -/
theorem full_endpoint_cases (C : PairConfiguration d)
    (hc : d.HasProtectedCenter) :
    C.repeatedEnd ∈ N5.fullCornerTypes d ∨ C.otherEnd ∈ N5.fullCornerTypes d := by
  classical
  obtain ⟨v, hv⟩ := fullCornerTypes_nonempty d hc C.incidence_count
  have hvend := C.full_types_subset_endpoints hc hv
  rcases Finset.mem_insert.mp hvend with hvb | hvr
  · exact Or.inl (hvb ▸ hv)
  · exact Or.inr (Finset.mem_singleton.mp hvr ▸ hv)

/-- A full repeated endpoint accounts for exactly two uniquely owned
physical square corners. -/
theorem unique_corner_count_two_of_repeatedEnd_full (C : PairConfiguration d)
    (hc : d.HasProtectedCenter) (hb : C.repeatedEnd ∈ N5.fullCornerTypes d) :
    (Finset.univ.filter fun j : Fin 4 => d.cornerTileCount j = 1).card = 2 := by
  have hr : C.otherEnd ∉ N5.fullCornerTypes d :=
    fun hr => C.not_both_endpoints_full hc ⟨hb, hr⟩
  simpa only [if_pos hb, if_neg hr, add_zero] using C.unique_corner_count_formula hc

/-- A full other endpoint accounts for exactly one uniquely owned
physical square corner. -/
theorem unique_corner_count_one_of_otherEnd_full (C : PairConfiguration d)
    (hc : d.HasProtectedCenter) (hr : C.otherEnd ∈ N5.fullCornerTypes d) :
    (Finset.univ.filter fun j : Fin 4 => d.cornerTileCount j = 1).card = 1 := by
  have hb : C.repeatedEnd ∉ N5.fullCornerTypes d :=
    fun hb => C.not_both_endpoints_full hc ⟨hb, hr⟩
  simpa only [if_neg hb, if_pos hr, zero_add] using C.unique_corner_count_formula hc

/-- If the repeated endpoint is full, it is the only full intrinsic type. -/
theorem full_types_eq_repeatedEnd_of_full (C : PairConfiguration d)
    (hc : d.HasProtectedCenter) (hb : C.repeatedEnd ∈ N5.fullCornerTypes d) :
    N5.fullCornerTypes d = {C.repeatedEnd} := by
  classical
  apply Finset.eq_singleton_iff_unique_mem.mpr
  refine ⟨hb, fun v hv => ?_⟩
  rcases Finset.mem_insert.mp (C.full_types_subset_endpoints hc hv) with hvb | hvr
  · exact hvb
  · exact False.elim (C.not_both_endpoints_full hc
      ⟨hb, Finset.mem_singleton.mp hvr ▸ hv⟩)

/-- If the other endpoint is full, it is the only full intrinsic type. -/
theorem full_types_eq_otherEnd_of_full (C : PairConfiguration d)
    (hc : d.HasProtectedCenter) (hr : C.otherEnd ∈ N5.fullCornerTypes d) :
    N5.fullCornerTypes d = {C.otherEnd} := by
  classical
  apply Finset.eq_singleton_iff_unique_mem.mpr
  refine ⟨hr, fun v hv => ?_⟩
  rcases Finset.mem_insert.mp (C.full_types_subset_endpoints hc hv) with hvb | hvr
  · exact False.elim (C.not_both_endpoints_full hc ⟨hvb ▸ hv, hr⟩)
  · exact Finset.mem_singleton.mp hvr

/-- A single uniquely owned physical corner forces the other endpoint to
be the unique full type. -/
theorem full_types_eq_otherEnd_of_unique_count_one (C : PairConfiguration d)
    (hc : d.HasProtectedCenter)
    (hcount : (Finset.univ.filter fun j : Fin 4 => d.cornerTileCount j = 1).card = 1) :
    N5.fullCornerTypes d = {C.otherEnd} := by
  rcases C.full_endpoint_cases hc with hb | hr
  · have htwo := C.unique_corner_count_two_of_repeatedEnd_full hc hb
    omega
  · exact C.full_types_eq_otherEnd_of_full hc hr

/-- Two uniquely owned physical corners force the repeated endpoint to
be the unique full type. -/
theorem full_types_eq_repeatedEnd_of_unique_count_two (C : PairConfiguration d)
    (hc : d.HasProtectedCenter)
    (hcount : (Finset.univ.filter fun j : Fin 4 => d.cornerTileCount j = 1).card = 2) :
    N5.fullCornerTypes d = {C.repeatedEnd} := by
  rcases C.full_endpoint_cases hc with hb | hr
  · exact C.full_types_eq_repeatedEnd_of_full hc hb
  · have hone := C.unique_corner_count_one_of_otherEnd_full hc hr
    omega

end

end Puzzling139335.N7.PairConfiguration
