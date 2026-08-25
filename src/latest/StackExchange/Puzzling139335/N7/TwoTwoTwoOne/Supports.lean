import StackExchange.Puzzling139335.N7.FullTypes
import StackExchange.Puzzling139335.AcuteCorner
import StackExchange.Puzzling139335.DoubleCorner

/-!
# Supporting cones used by the `2221` branch

These lemmas use actual prototype points and the actual placement maps.
A forty-five-degree support point must occur in every two-corner pair;
in particular the endpoint omitted by the third pair cannot have such a
support.  Supports also transport to any actual double-corner occurrence.
-/

open Set

namespace Puzzling139335.N7.TwoTwoTwoOne

open N8 AcuteCorner

/-- Every supported prototype point must be present in each actual
two-corner placement. -/
theorem support45_mem_intrinsicPair (d : SquareDissection)
    (hc : d.HasProtectedCenter) (i : Fin 4) (hcount : d.tileCornerCount i = 2)
    {v : Plane} (hv : v ∈ d.piece 0) (hsupport : Supports45 (d.piece 0) v) :
    v ∈ intrinsicPair d i := by
  classical
  obtain ⟨s, hs⟩ := exists_local_side_of_count_two d hc i hcount
  have hne : s ≠ s + 1 := by
    fin_cases s <;> decide
  have hside := d.support45_preimage_eq_of_two_corners hc i s (s + 1) hne
    ((hs s).mpr (Or.inl rfl)) ((hs (s + 1)).mpr (Or.inr rfl))
    (d.placement i) (d.placement_image i) hv hsupport
  rw [local_intrinsicPair_eq d hs]
  simpa only [Finset.mem_insert, Finset.mem_singleton, SquareDissection.intrinsicCorner]
    using hside

/-- Transport a prototype support to an actual double-corner occurrence;
the square center is outside that piece's interior. -/
theorem center_excluded_of_supported_type (d : SquareDissection)
    {i k j : Fin 4} (hik : i ≠ k)
    (hi : corner j ∈ d.piece i) (hk : corner j ∈ d.piece k)
    (hother : ∀ l, l ≠ i → l ≠ k → corner j ∉ d.piece l)
    {v : Plane} (htype : d.intrinsicCorner i j = v)
    (hsupport : Supports45 (d.piece 0) v) :
    squareCenter ∉ interior (d.piece i) := by
  have hsupport' := hsupport.image (d.placement i)
  have hv : d.placement i v = corner j := by
    rw [← htype, d.placement_intrinsicCorner]
  rw [d.placement_image, hv] at hsupport'
  exact d.center_excluded_at_double_corner_of_support hik hi hk hother hsupport'

end Puzzling139335.N7.TwoTwoTwoOne

namespace Puzzling139335.N7.PairConfiguration

open N8 AcuteCorner TwoTwoTwoOne

variable {d : SquareDissection}

/-- The third pair omits the repeated endpoint, so that prototype point
cannot support the piece in a forty-five-degree cone. -/
theorem repeatedEnd_not_support45 (C : PairConfiguration d)
    (hc : d.HasProtectedCenter) : ¬ Supports45 (d.piece 0) C.repeatedEnd := by
  classical
  intro hsupport
  have hused : C.repeatedEnd ∈ d.usedCornerTypes := by rw [C.types]; simp
  have hpair := support45_mem_intrinsicPair d hc (C.double 2) (C.double_count 2)
    (d.usedCornerTypes_subset hused) hsupport
  rw [C.pair_two] at hpair
  simp [C.common_ne_repeatedEnd.symm, C.repeatedEnd_ne_otherEnd] at hpair

/-- Two occurrences of the repeated endpoint cannot fill one square
corner: they would force the forbidden supporting cone. -/
theorem no_repeatedEnd_double_corner (C : PairConfiguration d)
    (hc : d.HasProtectedCenter) {i k j : Fin 4} (hik : i ≠ k)
    (hi : corner j ∈ d.piece i) (hk : corner j ∈ d.piece k)
    (hother : ∀ l, l ≠ i → l ≠ k → corner j ∉ d.piece l)
    (hti : d.intrinsicCorner i j = C.repeatedEnd)
    (htk : d.intrinsicCorner k j = C.repeatedEnd) : False := by
  apply C.repeatedEnd_not_support45 hc
  simpa only [hti] using d.same_intrinsic_double_corner_prototype_support
    hik hi hk hother (hti.trans htk.symm)

/-- In the one-unique-corner branch, the repeated endpoint is not full. -/
theorem repeatedEnd_not_full_of_unique_count_one (C : PairConfiguration d)
    (hc : d.HasProtectedCenter)
    (hU : (Finset.univ.filter fun j : Fin 4 => d.cornerTileCount j = 1).card = 1) :
    C.repeatedEnd ∉ N5.fullCornerTypes d := by
  classical
  rw [C.full_types_eq_otherEnd_of_unique_count_one hc hU]
  simpa only [Finset.mem_singleton] using C.repeatedEnd_ne_otherEnd

end Puzzling139335.N7.PairConfiguration
