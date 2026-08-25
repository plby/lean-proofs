import StackExchange.Puzzling139335.N7.FullPairNormalization.FullCorner

/-!
# The third pair lies on the right after full-pair normalization

The repeated full endpoint gives uniquely owned bottom-left and top-left
corners.  Every other piece can therefore use only the right corners.
The third double-corner piece has two distinct actual intrinsic endpoints,
so its ordered images occupy the right side in one of two orientations.
-/

open Set

namespace Puzzling139335.N7.PairConfiguration

open N8 SquareSymmetry FullPairNormalization

noncomputable section

variable {d : SquareDissection}

/-- Every square corner of any piece other than the normalized repeated
pair is a right corner. -/
theorem normalized_other_piece_corners_on_right (C : PairConfiguration d)
    (hc : d.HasProtectedCenter) (hfull : C.repeatedEnd ∈ N5.fullCornerTypes d)
    (f : Plane ≃ᵃⁱ[ℝ] Plane) (hfS : f '' unitSquare = unitSquare)
    (hfR : f (d.placement (C.double 0) C.repeatedEnd) = corner 0)
    (hfA : f (d.placement (C.double 0) C.common) = corner 1)
    {i j : Fin 4} (hi0 : i ≠ C.double 0) (hi1 : i ≠ C.double 1)
    (hj : corner j ∈ (d.map f hfS).piece i) : j = 1 ∨ j = 2 := by
  classical
  have hR0 : C.repeatedEnd ∈ intrinsicPair d (C.double 0) := by
    rw [C.pair_zero]
    simp
  have hR1 : C.repeatedEnd ∈ intrinsicPair d (C.double 1) := by
    rw [C.pair_one]
    simp
  have hRtop := (C.repeated_full_pair_endpoints hc hfull f hfS hfR hfA).1
  have hzeroCount : (d.map f hfS).cornerTileCount 0 = 1 :=
    corner_count_one_of_placed_full_type d hR0 hfull f hfS hfR
  have htopCount : (d.map f hfS).cornerTileCount 3 = 1 :=
    corner_count_one_of_placed_full_type d hR1 hfull f hfS hRtop
  have hzeroMem : corner 0 ∈ (d.map f hfS).piece (C.double 0) :=
    placed_intrinsic_mem_map d hR0 f hfS hfR
  have htopMem : corner 3 ∈ (d.map f hfS).piece (C.double 1) :=
    placed_intrinsic_mem_map d hR1 f hfS hRtop
  fin_cases j
  · exact ((d.map f hfS).unique_corner_owner_of_count_one
      hzeroCount hzeroMem i hi0 hj).elim
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact ((d.map f hfS).unique_corner_owner_of_count_one
      htopCount htopMem i hi1 hj).elim

/-- The third double-corner piece has exactly the two possible ordered
endpoint placements on the right side. -/
theorem normalized_third_pair_orientation (C : PairConfiguration d)
    (hc : d.HasProtectedCenter) (hfull : C.repeatedEnd ∈ N5.fullCornerTypes d)
    (f : Plane ≃ᵃⁱ[ℝ] Plane) (hfS : f '' unitSquare = unitSquare)
    (hfR : f (d.placement (C.double 0) C.repeatedEnd) = corner 0)
    (hfA : f (d.placement (C.double 0) C.common) = corner 1) :
    (f (d.placement (C.double 2) C.common) = corner 2 ∧
      f (d.placement (C.double 2) C.otherEnd) = corner 1) ∨
    (f (d.placement (C.double 2) C.common) = corner 1 ∧
      f (d.placement (C.double 2) C.otherEnd) = corner 2) := by
  classical
  have hi0 : C.double 2 ≠ C.double 0 := C.double_injective.ne (by decide)
  have hi1 : C.double 2 ≠ C.double 1 := C.double_injective.ne (by decide)
  have hright (v : Plane) (hv : v ∈ intrinsicPair d (C.double 2)) :
      f (d.placement (C.double 2) v) = corner 1 ∨
        f (d.placement (C.double 2) v) = corner 2 := by
    obtain ⟨a, ha, hva⟩ := (mem_intrinsicPair d (C.double 2) v).mp hv
    have hp : d.placement (C.double 2) v = corner a := by
      rw [← hva, d.placement_intrinsicCorner]
    obtain ⟨j, hj⟩ := maps_corner_of_maps_square_into_square f hfS.subset a
    have hfv : f (d.placement (C.double 2) v) = corner j := by rw [hp, hj]
    have hjmem := placed_intrinsic_mem_map d hv f hfS hfv
    rcases C.normalized_other_piece_corners_on_right hc hfull f hfS hfR hfA
        hi0 hi1 hjmem with rfl | rfl
    · exact Or.inl hfv
    · exact Or.inr hfv
  have hcommon : C.common ∈ intrinsicPair d (C.double 2) := by
    rw [C.pair_two]
    simp
  have hother : C.otherEnd ∈ intrinsicPair d (C.double 2) := by
    rw [C.pair_two]
    simp
  have hne : f (d.placement (C.double 2) C.common) ≠
      f (d.placement (C.double 2) C.otherEnd) :=
    (f.injective.comp (d.placement (C.double 2)).injective).ne C.common_ne_otherEnd
  rcases hright C.common hcommon with hA | hA <;>
    rcases hright C.otherEnd hother with hB | hB
  · exact (hne (hA.trans hB.symm)).elim
  · exact Or.inr ⟨hA, hB⟩
  · exact Or.inl ⟨hA, hB⟩
  · exact (hne (hA.trans hB.symm)).elim

end

end Puzzling139335.N7.PairConfiguration
