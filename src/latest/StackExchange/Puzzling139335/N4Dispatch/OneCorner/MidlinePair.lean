import StackExchange.Puzzling139335.N4Midline
import StackExchange.Puzzling139335.FourIncidences
import StackExchange.Puzzling139335.SymmetryOrbit
import StackExchange.Puzzling139335.ReflectionSeparation.Maps

/-!
# The actual midline pair in the one-corner case

The two upper corner preimages required by the normalized midline theorem
are derived from actual congruences. Reusing the origin would create three
square-symmetric copies. Reusing one upper preimage for both upper pieces
would exclude the center from the upper pieces as well as the reflected
lower pair.
-/

open Set

namespace Puzzling139335.N4Dispatch.OneCorner

open ReflectionSeparation

private theorem midline_corner_preimage_ne_zero (d : SquareDissection)
    (hN : d.cornerIncidenceCount = 4) (hzero : corner 0 ∈ d.piece 0)
    (hmirror : vertical '' d.piece 0 = d.piece 1) (hc : d.HasProtectedCenter)
    {k : Fin 4} (hk0 : k ≠ 0) (hk1 : k ≠ 1)
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
    (by decide : (0 : Fin 4) ≠ 1) (Ne.symm hk0) (Ne.symm hk1)
    vertical e vertical_image_unitSquare.subset heS.subset hmirror he hc

/-- The upper intrinsic corner preimages are distinct and nonzero; this is
a consequence of actual dissection geometry, independent of chosen types. -/
theorem midline_corner_preimages_distinct (d : SquareDissection)
    (hN : d.cornerIncidenceCount = 4)
    (hOwners : ∀ j : Fin 4, corner j ∈ d.piece j)
    (hmirror : vertical '' d.piece 0 = d.piece 1) (hc : d.HasProtectedCenter)
    (r t : Plane ≃ᵃⁱ[ℝ] Plane)
    (hr : r '' d.piece 0 = d.piece 2) (ht : t '' d.piece 0 = d.piece 3) :
    r.symm (corner 2) ≠ 0 ∧ t.symm (corner 3) ≠ 0 ∧
      r.symm (corner 2) ≠ t.symm (corner 3) := by
  refine ⟨midline_corner_preimage_ne_zero d hN (hOwners 0) hmirror hc
    (by decide) (by decide) r hr,
    midline_corner_preimage_ne_zero d hN (hOwners 0) hmirror hc
      (by decide) (by decide) t ht, ?_⟩
  intro hpre
  have hrelative : (r.symm.trans t) '' d.piece 2 = d.piece 3 := by
    calc
      (r.symm.trans t) '' d.piece 2 =
          (r.symm.trans t) '' (r '' d.piece 0) := by rw [hr]
      _ = t '' d.piece 0 := by
        simp only [image_image, AffineIsometryEquiv.coe_trans,
          Function.comp_apply, AffineIsometryEquiv.symm_apply_apply]
      _ = d.piece 3 := ht
  have hmap : (r.symm.trans t) (corner 2) = corner 3 := by
    change t (r.symm (corner 2)) = corner 3
    rw [hpre, t.apply_symm_apply]
  have hupper := d.center_not_mem_unique_corner_pair
    (by decide : (2 : Fin 4) ≠ 3) 2 3 (r.symm.trans t) hrelative hmap
    (d.unique_corner_owner_of_four_incidences hN (hOwners 2))
  have hlower := d.center_not_mem_fixed_pair (by decide : (0 : Fin 4) ≠ 1)
    vertical hmirror vertical_center
  obtain ⟨i, hi⟩ := hc
  fin_cases i
  · exact hlower.1 hi
  · exact hlower.2 hi
  · exact hupper.1 hi
  · exact hupper.2 hi

/-- The normalized midline obstruction needs only the actual reflected
pair and uniquely owned corner labels. -/
theorem midline_pair_not_protected (d : SquareDissection)
    (hN : d.cornerIncidenceCount = 4)
    (hOwners : ∀ j : Fin 4, corner j ∈ d.piece j)
    (hmirror : vertical '' d.piece 0 = d.piece 1) : ¬ d.HasProtectedCenter := by
  intro hc
  have hcorners : ∀ j i : Fin 4, corner j ∈ d.piece i ↔ j = i := by
    intro j i
    constructor
    · intro hj
      by_contra hne
      exact d.unique_corner_owner_of_four_incidences hN (hOwners j) i (Ne.symm hne) hj
    · intro hji
      rw [hji]
      exact hOwners i
  obtain ⟨r, hr⟩ := d.congruent 0 2
  obtain ⟨t, ht⟩ := d.congruent 0 3
  obtain ⟨hrzero, htzero, hrt⟩ :=
    midline_corner_preimages_distinct d hN hOwners hmirror hc r t hr ht
  exact N4Midline.normalized_midline_not_protected d hcorners hmirror r t hr ht
    hrzero htzero hrt hc

end Puzzling139335.N4Dispatch.OneCorner
