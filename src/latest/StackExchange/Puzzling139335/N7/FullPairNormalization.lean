import StackExchange.Puzzling139335.N7.FullTypes
import StackExchange.Puzzling139335.N7.UnsplitCorners
import StackExchange.Puzzling139335.N5.Transport
import StackExchange.Puzzling139335.N7.FullPairNormalization.Frame
import StackExchange.Puzzling139335.N7.FullPairNormalization.SquareAction

/-!
# Normalizing the repeated pair when its other endpoint is full

The repeated full endpoint occurs at two distinct uniquely owned corners.
Those corners are adjacent.  After putting the first repeated pair on the
bottom side with its full endpoint at bottom left, the second repeated pair
is therefore the top side, with the same endpoint order.  The actual relative
placement is conjugate to horizontal reflection.
-/

open Set

namespace Puzzling139335.N7

open N8 SquareSymmetry ReflectionSeparation FullPairNormalization

noncomputable section

private theorem exists_placed_corner {d : SquareDissection} {i : Fin 4} {v : Plane}
    (hv : v ∈ intrinsicPair d i) :
    ∃ a : Fin 4, corner a ∈ d.piece i ∧ d.intrinsicCorner i a = v ∧
      d.placement i v = corner a := by
  obtain ⟨a, ha, hav⟩ := (mem_intrinsicPair d i v).mp hv
  refine ⟨a, ha, hav, ?_⟩
  rw [← hav, d.placement_intrinsicCorner]

private theorem count_one_of_full_occurrence {d : SquareDissection} {i a : Fin 4}
    {v : Plane} (ha : corner a ∈ d.piece i) (hva : d.intrinsicCorner i a = v)
    (hv : v ∈ N5.fullCornerTypes d) : d.cornerTileCount a = 1 := by
  apply N5.corner_count_one_of_unique_owner d ha
  apply N5.unique_corner_of_type_mem_full d
  rwa [hva]

namespace PairConfiguration

variable {d : SquareDissection}

/-- The actual relative placement of the repeated pair preserves the square. -/
theorem repeated_pair_preserves_square (C : PairConfiguration d)
    (hc : d.HasProtectedCenter) :
    d.relativePlacement (C.double 0) (C.double 1) '' unitSquare = unitSquare := by
  obtain ⟨s, hs⟩ := exists_local_side_of_count_two d hc (C.double 0) (C.double_count 0)
  obtain ⟨t, ht⟩ := exists_local_side_of_count_two d hc (C.double 1) (C.double_count 1)
  exact local_relativePlacement_preserves_square_of_pair_eq d hs ht
    (C.pair_zero.trans C.pair_one.symm)

/-- Once the first pair is put on the bottom side in the stated order,
actual unique ownership forces the mate onto the top side in the same order. -/
theorem repeated_full_pair_endpoints (C : PairConfiguration d)
    (hc : d.HasProtectedCenter) (hfull : C.repeatedEnd ∈ N5.fullCornerTypes d)
    (f : Plane ≃ᵃⁱ[ℝ] Plane) (hfS : f '' unitSquare = unitSquare)
    (hfR : f (d.placement (C.double 0) C.repeatedEnd) = corner 0)
    (hfA : f (d.placement (C.double 0) C.common) = corner 1) :
    f (d.placement (C.double 1) C.repeatedEnd) = corner 3 ∧
      f (d.placement (C.double 1) C.common) = corner 2 := by
  classical
  have hR0 : C.repeatedEnd ∈ intrinsicPair d (C.double 0) := by rw [C.pair_zero]; simp
  have hA0 : C.common ∈ intrinsicPair d (C.double 0) := by rw [C.pair_zero]; simp
  have hR1 : C.repeatedEnd ∈ intrinsicPair d (C.double 1) := by rw [C.pair_one]; simp
  have hA1 : C.common ∈ intrinsicPair d (C.double 1) := by rw [C.pair_one]; simp
  obtain ⟨r0, hr0, htr0, hpr0⟩ := exists_placed_corner hR0
  obtain ⟨a0, ha0, hta0, hpa0⟩ := exists_placed_corner hA0
  obtain ⟨r1, hr1, htr1, hpr1⟩ := exists_placed_corner hR1
  obtain ⟨a1, ha1, hta1, hpa1⟩ := exists_placed_corner hA1
  have hfr0 : f (corner r0) = corner 0 := by rwa [hpr0] at hfR
  have hfa0 : f (corner a0) = corner 1 := by rwa [hpa0] at hfA
  obtain ⟨r, hfr1⟩ := maps_corner_of_maps_square_into_square f hfS.subset r1
  obtain ⟨a, hfa1⟩ := maps_corner_of_maps_square_into_square f hfS.subset a1
  let D := d.map f hfS
  have hcD : D.HasProtectedCenter := (d.map_hasProtectedCenter f hfS).mpr hc
  have hND : D.cornerIncidenceCount = 7 :=
    (N5.cornerIncidenceCount_map d f hfS).trans C.incidence_count
  have hr0count : d.cornerTileCount r0 = 1 :=
    count_one_of_full_occurrence hr0 htr0 hfull
  have hr1count : d.cornerTileCount r1 = 1 :=
    count_one_of_full_occurrence hr1 htr1 hfull
  have ha0not : d.cornerTileCount a0 ≠ 1 := by
    intro hcount
    exact C.common_not_full hc
      ((N5.mem_fullCornerTypes d).mpr ⟨C.double 0, a0, ha0, hcount, hta0⟩)
  have hzeroCount : D.cornerTileCount 0 = 1 :=
    (cornerTileCount_map_of_corner_image d f hfS hfr0).trans hr0count
  have hrCount : D.cornerTileCount r = 1 :=
    (cornerTileCount_map_of_corner_image d f hfS hfr1).trans hr1count
  have honeNot : D.cornerTileCount 1 ≠ 1 := by
    rw [cornerTileCount_map_of_corner_image d f hfS hfa0]
    exact ha0not
  have hzeroMem : corner 0 ∈ D.piece (C.double 0) := ⟨corner r0, hr0, hfr0⟩
  have hrMem : corner r ∈ D.piece (C.double 1) := ⟨corner r1, hr1, hfr1⟩
  have haMem : corner a ∈ D.piece (C.double 1) := ⟨corner a1, ha1, hfa1⟩
  have h10 : C.double 1 ≠ C.double 0 := C.double_injective.ne (by decide)
  have hr0ne : r ≠ 0 := by
    intro h
    exact D.unique_corner_owner_of_count_one hzeroCount hzeroMem
      (C.double 1) h10 (h ▸ hrMem)
  have hr1ne : r ≠ 1 := by
    intro h
    exact honeNot (h ▸ hrCount)
  have hr2ne : r ≠ 2 := by
    intro h
    apply opposite_corners_not_both_unique D hcD hND 0
    exact ⟨hzeroCount, by simpa only [h, zero_add] using hrCount⟩
  have hrEq : r = 3 := by
    fin_cases r
    · exact (hr0ne rfl).elim
    · exact (hr1ne rfl).elim
    · exact (hr2ne rfl).elim
    · rfl
  have hRtop : f (d.placement (C.double 1) C.repeatedEnd) = corner 3 := by
    rw [hpr1, hfr1, hrEq]
  have htopMem : corner 3 ∈ D.piece (C.double 1) := hrEq ▸ hrMem
  have ha0ne : a ≠ 0 := by
    intro h
    exact D.unique_corner_owner_of_count_one hzeroCount hzeroMem
      (C.double 1) h10 (h ▸ haMem)
  have ha1ne : a ≠ 1 := by
    intro h
    exact D.no_opposite_corners hcD (C.double 1) 1 ⟨h ▸ haMem, htopMem⟩
  have ha3ne : a ≠ 3 := by
    intro h
    apply C.common_ne_repeatedEnd
    apply (d.placement (C.double 1)).injective
    apply f.injective
    calc
      f (d.placement (C.double 1) C.common) = corner a := by rw [hpa1, hfa1]
      _ = corner 3 := by rw [h]
      _ = f (d.placement (C.double 1) C.repeatedEnd) := hRtop.symm
  have haEq : a = 2 := by
    fin_cases a
    · exact (ha0ne rfl).elim
    · exact (ha1ne rfl).elim
    · rfl
    · exact (ha3ne rfl).elim
  exact ⟨hRtop, by rw [hpa1, hfa1, haEq]⟩

/-- In these coordinates, the actual relative placement is horizontal
reflection, as an equality of affine isometries. -/
theorem horizontal_conjugate_of_repeated_full_pair (C : PairConfiguration d)
    (hc : d.HasProtectedCenter) (hfull : C.repeatedEnd ∈ N5.fullCornerTypes d)
    (f : Plane ≃ᵃⁱ[ℝ] Plane) (hfS : f '' unitSquare = unitSquare)
    (hfR : f (d.placement (C.double 0) C.repeatedEnd) = corner 0)
    (hfA : f (d.placement (C.double 0) C.common) = corner 1) :
    (f.symm.trans (d.relativePlacement (C.double 0) (C.double 1))).trans f =
      horizontal := by
  obtain ⟨hRtop, hAtop⟩ := C.repeated_full_pair_endpoints hc hfull f hfS hfR hfA
  let e := d.relativePlacement (C.double 0) (C.double 1)
  let g := (f.symm.trans e).trans f
  have hfinvS : f.symm '' unitSquare = unitSquare := by
    calc
      f.symm '' unitSquare = f.symm '' (f '' unitSquare) := by rw [hfS]
      _ = unitSquare := by
        simp only [image_image, f.symm_apply_apply, Set.image_id']
  have hgS : g '' unitSquare = unitSquare := by
    calc
      g '' unitSquare = f '' (e '' (f.symm '' unitSquare)) := by
        simp only [g, AffineIsometryEquiv.coe_trans, image_image, Function.comp_def]
      _ = unitSquare := by rw [hfinvS, C.repeated_pair_preserves_square hc, hfS]
  have hconj (v : Plane) :
      g (f (d.placement (C.double 0) v)) = f (d.placement (C.double 1) v) := by
    simp [g, e, SquareDissection.relativePlacement]
  apply eq_horizontal_of_bottom_endpoints g hgS
  · rw [← hfR, hconj, hRtop]
  · rw [← hfA, hconj, hAtop]

/-- A full repeated endpoint admits a square-preserving normalization with
the repeated pair on the bottom and top edges and horizontal relative map. -/
theorem exists_horizontal_pair_normalization (C : PairConfiguration d)
    (hc : d.HasProtectedCenter) (hfull : C.repeatedEnd ∈ N5.fullCornerTypes d) :
    ∃ f : Plane ≃ᵃⁱ[ℝ] Plane,
      f '' unitSquare = unitSquare ∧
      f (d.placement (C.double 0) C.repeatedEnd) = corner 0 ∧
      f (d.placement (C.double 0) C.common) = corner 1 ∧
      f (d.placement (C.double 1) C.repeatedEnd) = corner 3 ∧
      f (d.placement (C.double 1) C.common) = corner 2 ∧
      (f.symm.trans (d.relativePlacement (C.double 0) (C.double 1))).trans f =
        horizontal := by
  have hpair : intrinsicPair d (C.double 0) = {C.repeatedEnd, C.common} := by
    rw [C.pair_zero, Finset.pair_comm]
  obtain ⟨f, hfS, hfR, hfA⟩ := exists_ordered_pair_frame d hc (C.double 0)
    (C.double_count 0) C.repeatedEnd C.common C.common_ne_repeatedEnd.symm hpair
  obtain ⟨hRtop, hAtop⟩ := C.repeated_full_pair_endpoints hc hfull f hfS hfR hfA
  exact ⟨f, hfS, hfR, hfA, hRtop, hAtop,
    C.horizontal_conjugate_of_repeated_full_pair hc hfull f hfS hfR hfA⟩

end PairConfiguration

end

end Puzzling139335.N7
