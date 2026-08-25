import StackExchange.Puzzling139335.N7.FullPairNormalization.ThirdPair
import StackExchange.Puzzling139335.N7.FullPairNormalization.Swap

/-!
# Fixing the orientation of the third pair

Horizontal reflection of the whole square, together with exchange of the
two repeated-pair copies, preserves the established bottom/top normalization.
This leaves the common endpoint of the third pair at top right and its other
endpoint at bottom right.
-/

open Set

namespace Puzzling139335.N7.PairConfiguration

open ReflectionSeparation

noncomputable section

variable {d : SquareDissection}

private theorem horizontal_corner_zero : horizontal (corner 0) = corner 3 := by
  ext k
  fin_cases k <;> norm_num [corner, Fin.ext_iff]

private theorem horizontal_corner_one : horizontal (corner 1) = corner 2 := by
  ext k
  fin_cases k <;> norm_num [corner, Fin.ext_iff]

private theorem horizontal_corner_two : horizontal (corner 2) = corner 1 := by
  ext k
  fin_cases k <;> norm_num [corner, Fin.ext_iff]

private theorem horizontal_corner_three : horizontal (corner 3) = corner 0 := by
  ext k
  fin_cases k <;> norm_num [corner, Fin.ext_iff]

/-- Choose which repeated-pair copy is the bottom piece so that the third
pair has its common endpoint at top right.  All six endpoint identities
concern the actual chosen placements of the original dissection. -/
theorem exists_oriented_pair_normalization (C : PairConfiguration d)
    (hc : d.HasProtectedCenter) (hfull : C.repeatedEnd ∈ N5.fullCornerTypes d) :
    ∃ (n0 n1 : Fin 3) (f : Plane ≃ᵃⁱ[ℝ] Plane),
      ((n0 = 0 ∧ n1 = 1) ∨ (n0 = 1 ∧ n1 = 0)) ∧
      f '' unitSquare = unitSquare ∧
      f (d.placement (C.double n0) C.repeatedEnd) = corner 0 ∧
      f (d.placement (C.double n0) C.common) = corner 1 ∧
      f (d.placement (C.double n1) C.repeatedEnd) = corner 3 ∧
      f (d.placement (C.double n1) C.common) = corner 2 ∧
      f (d.placement (C.double 2) C.common) = corner 2 ∧
      f (d.placement (C.double 2) C.otherEnd) = corner 1 ∧
      (f.symm.trans (d.relativePlacement (C.double n0) (C.double n1))).trans f =
        horizontal := by
  obtain ⟨f, hfS, hfR, hfA, hRtop, hAtop, hconj⟩ :=
    C.exists_horizontal_pair_normalization hc hfull
  rcases C.normalized_third_pair_orientation hc hfull f hfS hfR hfA with hthird | hthird
  · exact ⟨0, 1, f, Or.inl ⟨rfl, rfl⟩, hfS, hfR, hfA, hRtop, hAtop,
      hthird.1, hthird.2, hconj⟩
  · let f' := f.trans horizontal
    have hf'S : f' '' unitSquare = unitSquare := by
      calc
        f' '' unitSquare = horizontal '' (f '' unitSquare) := by
          simp only [f', AffineIsometryEquiv.coe_trans, image_image, Function.comp_def]
        _ = unitSquare := by rw [hfS, horizontal_image_unitSquare]
    have hfR' : f' (d.placement (C.double 1) C.repeatedEnd) = corner 0 := by
      change horizontal (f (d.placement (C.double 1) C.repeatedEnd)) = corner 0
      rw [hRtop, horizontal_corner_three]
    have hfA' : f' (d.placement (C.double 1) C.common) = corner 1 := by
      change horizontal (f (d.placement (C.double 1) C.common)) = corner 1
      rw [hAtop, horizontal_corner_two]
    have hRtop' : f' (d.placement (C.double 0) C.repeatedEnd) = corner 3 := by
      change horizontal (f (d.placement (C.double 0) C.repeatedEnd)) = corner 3
      rw [hfR, horizontal_corner_zero]
    have hAtop' : f' (d.placement (C.double 0) C.common) = corner 2 := by
      change horizontal (f (d.placement (C.double 0) C.common)) = corner 2
      rw [hfA, horizontal_corner_one]
    have hAthird' : f' (d.placement (C.double 2) C.common) = corner 2 := by
      change horizontal (f (d.placement (C.double 2) C.common)) = corner 2
      rw [hthird.1, horizontal_corner_one]
    have hBthird' : f' (d.placement (C.double 2) C.otherEnd) = corner 1 := by
      change horizontal (f (d.placement (C.double 2) C.otherEnd)) = corner 1
      rw [hthird.2, horizontal_corner_two]
    have hconj' :
        (f'.symm.trans (d.relativePlacement (C.double 1) (C.double 0))).trans f' =
          horizontal := by
      have h := C.swapRepeated.horizontal_conjugate_of_repeated_full_pair
        hc hfull f' hf'S
        (by simpa only [swapRepeated_double_zero, swapRepeated_repeatedEnd] using hfR')
        (by simpa only [swapRepeated_double_zero, swapRepeated_common] using hfA')
      simpa only [swapRepeated_double_zero, swapRepeated_double_one] using h
    exact ⟨1, 0, f', Or.inr ⟨rfl, rfl⟩, hf'S, hfR', hfA', hRtop', hAtop',
      hAthird', hBthird', hconj'⟩

end

end Puzzling139335.N7.PairConfiguration
