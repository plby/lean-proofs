import StackExchange.Puzzling139335.FourIncidences
import StackExchange.Puzzling139335.ReflectionSeparation.Maps
import StackExchange.Puzzling139335.SymmetryOrbit

/-!
# Distinct actual corner preimages in the diagonal reflection case

The reflected pair cannot own a center neighborhood. Reusing either its
intrinsic corner or the same intrinsic corner in both remaining pieces
would give actual square-preserving congruences and exclude every possible
owner of a center neighborhood.
-/

open Set

namespace Puzzling139335.N4Diagonal.FromDissection

open ReflectionSeparation

/-- The anti-diagonal pair fixes the center, so only the other two pieces
can contain a neighborhood of it. -/
theorem center_mem_one_or_three (d : SquareDissection)
    (hH : antiDiagonal '' d.piece 0 = d.piece 2)
    (hc : d.HasProtectedCenter) :
    squareCenter ∈ interior (d.piece 1) ∨
      squareCenter ∈ interior (d.piece 3) := by
  have hnot := d.center_not_mem_fixed_pair (by decide : (0 : Fin 4) ≠ 2)
    antiDiagonal hH antiDiagonal_center
  obtain ⟨i, hi⟩ := hc
  fin_cases i
  · exact False.elim (hnot.1 hi)
  · exact Or.inl hi
  · exact False.elim (hnot.2 hi)
  · exact Or.inr hi

private theorem corner_preimage_ne_zero (d : SquareDissection)
    (hN : d.cornerIncidenceCount = 4)
    (hzero : corner 0 ∈ d.piece 0)
    (hH : antiDiagonal '' d.piece 0 = d.piece 2)
    (hc : d.HasProtectedCenter) {k : Fin 4}
    (hk0 : k ≠ 0) (hk2 : k ≠ 2)
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (he : e '' d.piece 0 = d.piece k) :
    e.symm (corner k) ≠ 0 := by
  intro hpre
  have hcorner0 : corner 0 = (0 : Plane) := by
    ext i
    fin_cases i <;> norm_num [corner, Fin.ext_iff]
  have hmap : e (corner 0) = corner k := by
    rw [hcorner0, ← hpre, e.apply_symm_apply]
  have heS := d.unique_corner_congruence_preserves_square 0 k 0 k e he hmap
    (d.unique_corner_owner_of_four_incidences hN hzero)
  exact d.not_hasProtectedCenter_of_three_square_symmetry_copies
    (by decide : (0 : Fin 4) ≠ 2) (Ne.symm hk0) (Ne.symm hk2)
    antiDiagonal e antiDiagonal_image_unitSquare.subset heS.subset hH he hc

/-- The two remaining placements supply two distinct nonzero intrinsic
corner points in the source piece. -/
theorem corner_preimages_distinct (d : SquareDissection)
    (hN : d.cornerIncidenceCount = 4)
    (hOwners : ∀ j : Fin 4, corner j ∈ d.piece j)
    (hH : antiDiagonal '' d.piece 0 = d.piece 2)
    (hc : d.HasProtectedCenter)
    (e f : Plane ≃ᵃⁱ[ℝ] Plane)
    (he : e '' d.piece 0 = d.piece 1)
    (hf : f '' d.piece 0 = d.piece 3) :
    e.symm (corner 1) ≠ 0 ∧ f.symm (corner 3) ≠ 0 ∧
      e.symm (corner 1) ≠ f.symm (corner 3) := by
  refine ⟨corner_preimage_ne_zero d hN (hOwners 0) hH hc
    (by decide) (by decide) e he,
    corner_preimage_ne_zero d hN (hOwners 0) hH hc
      (by decide) (by decide) f hf, ?_⟩
  intro hpre
  have hrelative : (e.symm.trans f) '' d.piece 1 = d.piece 3 := by
    calc
      (e.symm.trans f) '' d.piece 1 =
          (e.symm.trans f) '' (e '' d.piece 0) := by rw [he]
      _ = f '' d.piece 0 := by
        simp only [image_image, AffineIsometryEquiv.coe_trans,
          Function.comp_apply, AffineIsometryEquiv.symm_apply_apply]
      _ = d.piece 3 := hf
  have hmap : (e.symm.trans f) (corner 1) = corner 3 := by
    change f (e.symm (corner 1)) = corner 3
    rw [hpre, f.apply_symm_apply]
  have hnot := d.center_not_mem_unique_corner_pair
    (by decide : (1 : Fin 4) ≠ 3) 1 3 (e.symm.trans f) hrelative hmap
    (d.unique_corner_owner_of_four_incidences hN (hOwners 1))
  exact (center_mem_one_or_three d hH hc).elim hnot.1 hnot.2

end Puzzling139335.N4Diagonal.FromDissection
