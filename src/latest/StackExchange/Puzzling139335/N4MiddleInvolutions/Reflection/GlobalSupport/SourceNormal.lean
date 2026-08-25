import StackExchange.Puzzling139335.N4MiddleInvolutions.Reflection.Hull
import StackExchange.Puzzling139335.N4MiddleInvolutions.Reflection.SupportTransport
import StackExchange.Puzzling139335.N4OuterPair.AxisNonzero

/-! A globally supporting image of the outer unit base supplies an oblique
unit supporting normal of the actual middle hull. -/

open Set

namespace Puzzling139335.N4MiddleInvolutions.Reflection

open FaceBounds PlaneIsometries

/-- If the entire middle union lies above the source base in the coordinates
of an actual placement, that base gives a unit supporting normal of its hull
with nonzero real coordinate. -/
theorem exists_oblique_unit_normal_of_global_base_support {d : SquareDissection}
    (h : N4OuterPair.Configuration d) (hc : d.HasProtectedCenter)
    (f : Plane ≃ᵃⁱ[ℝ] Plane) (hf : f '' d.piece 0 = d.piece 2)
    (hsupport : ∀ z ∈ d.piece 2 ∪ d.piece 3, 0 ≤ (f.symm z) 1) :
    ∃ z ∈ complexUnitSupportingNormals (middleHull d), z.re ≠ 0 := by
  let V : Set Plane := f.symm '' middleUnion d
  have hleft : corner 0 ∈ V := by
    refine ⟨f (corner 0), Or.inl ?_, f.symm_apply_apply _⟩
    exact hf ▸ mem_image_of_mem f h.bottom_left
  have hright : corner 1 ∈ V := by
    refine ⟨f (corner 1), Or.inl ?_, f.symm_apply_apply _⟩
    exact hf ▸ mem_image_of_mem f h.bottom_right
  have hheight : ∀ p ∈ V, 0 ≤ p 1 := by
    rintro _ ⟨z, hz, rfl⟩
    exact hsupport z hz
  have hbase : SupportsSegment V 0 (-1) (corner 0) (corner 1) := by
    refine ⟨hleft, hright, ?_, ?_⟩
    · intro p hp
      simpa [supportValue, corner] using neg_nonpos.mpr (hheight p hp)
    · intro p hp
      simpa [supportValue, corner] using neg_nonpos.mpr (hheight p hp)
  have himage : f '' V = middleUnion d := by
    simp [V, Set.image_image]
  have hface : SupportsSegment (middleHull d)
      (normalImage f 0 (-1) 0) (normalImage f 0 (-1) 1)
      (f (corner 0)) (f (corner 1)) := by
    have htransport := hbase.image_affineIsometry f
    rw [himage] at htransport
    exact htransport.convexHull
  have hunit := normalImage_unit f (by norm_num : (0 : ℝ) ^ 2 + (-1) ^ 2 = 1)
  have hlen : 1 ≤ dist (f (corner 0)) (f (corner 1)) := by
    rw [f.isometry.dist_eq]
    have hsq : dist (corner 0) (corner 1) ^ 2 = 1 := by
      norm_num [plane_dist_sq, corner, Fin.ext_iff]
    nlinarith [dist_nonneg (x := corner 0) (y := corner 1)]
  have hnormal : normalImage f 0 (-1) 0 = -linearMatrix f 0 1 := by
    have hv : (!₂[0, -1] : Plane) = -EuclideanSpace.single 1 1 := by
      ext i
      fin_cases i <;> simp
    simp only [normalImage, hv, map_neg, PiLp.neg_apply, linearMatrix]
  refine ⟨complexEquiv (normalImage f 0 (-1)), ?_, ?_⟩
  · exact complexEquiv_mem_complexSupportingNormalsAtLeast.mpr
      ⟨hunit, f (corner 0), f (corner 1), hface, hlen⟩
  · rw [complexEquiv_re, hnormal]
    exact neg_ne_zero.mpr (h.middle_normal_nonaxis hc (Or.inl rfl) f hf).2

end Puzzling139335.N4MiddleInvolutions.Reflection
