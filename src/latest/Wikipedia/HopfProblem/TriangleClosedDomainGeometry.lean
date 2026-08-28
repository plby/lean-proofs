import Wikipedia.HopfProblem.SpecialPeriodsTriangleTilingHalf
import Mathlib.Analysis.Complex.ReImTopology

/-!
# The full finite closure of the source triangle

The global height-shift homeomorphism identifies the actual triangle
interior with an open vertical half-strip.  Closing that product of
intervals and pulling back proves density at every finite boundary point,
including both elliptic corners.  The resulting closed region is the
actual left half-Ford region and has a uniform positive height floor.
-/

noncomputable section

open Set UpperHalfPlane
open scoped Topology

namespace Wikipedia.HopfProblem.SpecialPeriods.Triangle

/-- The actual finite closed half-Ford triangle in the complex plane. -/
def triangleClosedRegion : Set ℂ := {z |
  stripLeft ≤ z.re ∧ z.re ≤ -1 / 2 ∧ 0 < z.im ∧ 1 ≤ ‖z + 1‖}

/-- The semicircular boundary stays strictly above the real line on the
entire closed horizontal interval, including its endpoints. -/
theorem boundaryHeight_pos_of_closed_bounds {x : ℝ}
    (hl : stripLeft ≤ x) (hr : x ≤ -1 / 2) : 0 < boundaryHeight x := by
  have hlo : 0 < x + 2 := by linarith [neg_two_lt_stripLeft]
  have hhi : 0 < -x := by linarith
  apply Real.sqrt_pos.mpr
  nlinarith [mul_pos hlo hhi]

/-- On the closed horizontal interval the upper exterior of the circle
is exactly the non-strict epigraph of its positive boundary height. -/
theorem circle_closed_epigraph_iff {z : ℂ}
    (hl : stripLeft ≤ z.re) (hr : z.re ≤ -1 / 2) :
    (0 < z.im ∧ 1 ≤ ‖z + 1‖) ↔ boundaryHeight z.re ≤ z.im := by
  have hnorm : ‖z + 1‖ ^ 2 = (z.re + 1) ^ 2 + z.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq]
    simp [Complex.normSq_apply, pow_two]
  constructor
  · rintro ⟨hy, hn⟩
    apply (Real.sqrt_le_left hy.le).mpr
    have hs := (sq_le_sq₀ (show (0 : ℝ) ≤ 1 by norm_num)
      (norm_nonneg (z + 1))).mpr hn
    nlinarith
  · intro hh
    have hy : 0 < z.im := (boundaryHeight_pos_of_closed_bounds hl hr).trans_le hh
    refine ⟨hy, ?_⟩
    apply (sq_le_sq₀ (show (0 : ℝ) ≤ 1 by norm_num) (norm_nonneg (z + 1))).mp
    have hs := (Real.sqrt_le_left hy.le).mp hh
    nlinarith

theorem mem_triangleClosedRegion_iff_epigraph (z : ℂ) :
    z ∈ triangleClosedRegion ↔
      stripLeft ≤ z.re ∧ z.re ≤ -1 / 2 ∧ boundaryHeight z.re ≤ z.im := by
  constructor
  · rintro ⟨hl, hr, hi, hn⟩
    exact ⟨hl, hr, (circle_closed_epigraph_iff hl hr).mp ⟨hi, hn⟩⟩
  · rintro ⟨hl, hr, hh⟩
    exact ⟨hl, hr, (circle_closed_epigraph_iff hl hr).mpr hh⟩

/-- The closed vertical half-strip after subtracting the boundary height. -/
def triangleClosedStrip : Set ℂ := {z |
  stripLeft ≤ z.re ∧ z.re ≤ -1 / 2 ∧ 0 ≤ z.im}

theorem triangleOpenStrip_eq_reProdIm :
    triangleOpenStrip = (Ioo stripLeft (-1 / 2)) ×ℂ (Ioi 0) := by
  ext z
  change (stripLeft < z.re ∧ z.re < -1 / 2 ∧ 0 < z.im) ↔
    ((stripLeft < z.re ∧ z.re < -1 / 2) ∧ 0 < z.im)
  exact and_assoc.symm

theorem triangleClosedStrip_eq_reProdIm :
    triangleClosedStrip = (Icc stripLeft (-1 / 2)) ×ℂ (Ici 0) := by
  ext z
  change (stripLeft ≤ z.re ∧ z.re ≤ -1 / 2 ∧ 0 ≤ z.im) ↔
    ((stripLeft ≤ z.re ∧ z.re ≤ -1 / 2) ∧ 0 ≤ z.im)
  exact and_assoc.symm

/-- Closing the actual open half-strip includes both vertical sides,
the bottom segment, and the two corner points. -/
theorem closure_triangleOpenStrip : closure triangleOpenStrip = triangleClosedStrip := by
  rw [triangleOpenStrip_eq_reProdIm, Complex.closure_reProdIm,
    closure_Ioo (show stripLeft ≠ -1 / 2 by linarith [stripLeft_lt_neg_one]),
    closure_Ioi, ← triangleClosedStrip_eq_reProdIm]

theorem interior_triangleClosedStrip : interior triangleClosedStrip = triangleOpenStrip := by
  rw [triangleClosedStrip_eq_reProdIm, Complex.interior_reProdIm,
    interior_Icc, interior_Ici, ← triangleOpenStrip_eq_reProdIm]

theorem triangleClosedRegion_eq_preimage_strip :
    triangleClosedRegion = triangleHeightShift ⁻¹' triangleClosedStrip := by
  ext z
  rw [mem_triangleClosedRegion_iff_epigraph]
  simp only [mem_preimage, triangleClosedStrip, mem_ofPred_eq,
    triangleHeightShift_re, triangleHeightShift_im, sub_nonneg]

/-- The literal finite closure of the actual source triangle, with no
boundary point omitted and no Jordan-domain hypothesis. -/
theorem closure_triangleInterior : closure triangleInterior = triangleClosedRegion := by
  rw [triangleInterior_eq_preimage_strip, ← triangleHeightShift.preimage_closure,
    closure_triangleOpenStrip, ← triangleClosedRegion_eq_preimage_strip]

theorem triangleClosedRegion_isClosed : IsClosed triangleClosedRegion := by
  rw [← closure_triangleInterior]
  exact isClosed_closure

/-- The strict inequalities give the whole interior of the proved closed region. -/
theorem interior_triangleClosedRegion : interior triangleClosedRegion = triangleInterior := by
  rw [triangleClosedRegion_eq_preimage_strip, ← triangleHeightShift.preimage_interior,
    interior_triangleClosedStrip, ← triangleInterior_eq_preimage_strip]

theorem triangleInterior_subset_closedRegion : triangleInterior ⊆ triangleClosedRegion := by
  rw [← closure_triangleInterior]
  exact subset_closure

theorem triangleClosedRegion_subset_closure : triangleClosedRegion ⊆ closure triangleInterior := by
  rw [closure_triangleInterior]

theorem triangleClosedRegion_im_pos {z : ℂ} (hz : z ∈ triangleClosedRegion) :
    0 < z.im := hz.2.2.1

/-- On the left half of the plane the extra Ford-circle inequality is
implied by the circle centred at `-1`, including equality on the cut. -/
theorem triangle_norm_add_one_le_norm {z : ℂ} (hz : z.re ≤ -1 / 2) :
    ‖z + 1‖ ≤ ‖z‖ := by
  apply (sq_le_sq₀ (norm_nonneg (z + 1)) (norm_nonneg z)).mp
  rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
  simp only [Complex.normSq_apply, Complex.add_re, Complex.one_re,
    Complex.add_im, Complex.one_im, add_zero]
  nlinarith

/-- The complex closed region is precisely the actual left half-Ford
region under the original upper-half-plane inclusion. -/
theorem coe_mem_triangleClosedRegion_iff_halfFordRegion (z : ℍ) :
    (z : ℂ) ∈ triangleClosedRegion ↔ z ∈ halfFordRegion := by
  change (stripLeft ≤ z.re ∧ z.re ≤ -1 / 2 ∧ 0 < z.im ∧ 1 ≤ ‖(z : ℂ) + 1‖) ↔
    ((stripLeft ≤ z.re ∧ z.re ≤ stripRight ∧
      1 ≤ ‖(z : ℂ) + 1‖ ∧ 1 ≤ ‖(z : ℂ)‖) ∧ z.re ≤ -(1 / 2))
  constructor
  · rintro ⟨hl, hr, _, hn⟩
    refine ⟨⟨hl, ?_, hn, hn.trans (triangle_norm_add_one_le_norm hr)⟩, by linarith⟩
    linarith [stripRight_pos]
  · rintro ⟨hz, hr⟩
    exact ⟨hz.1, by linarith, z.im_pos, hz.2.2.1⟩

theorem halfFordRegion_eq_preimage_triangleClosedRegion :
    halfFordRegion = ((↑) : ℍ → ℂ) ⁻¹' triangleClosedRegion :=
  Set.ext fun z => (coe_mem_triangleClosedRegion_iff_halfFordRegion z).symm

theorem triangleClosedRegion_eq_image_halfFordRegion :
    triangleClosedRegion = ((↑) : ℍ → ℂ) '' halfFordRegion := by
  ext z
  constructor
  · intro hz
    refine ⟨⟨z, triangleClosedRegion_im_pos hz⟩, ?_, rfl⟩
    exact (coe_mem_triangleClosedRegion_iff_halfFordRegion _).mp hz
  · rintro ⟨w, hw, rfl⟩
    exact (coe_mem_triangleClosedRegion_iff_halfFordRegion w).mpr hw

/-- The closed source triangle has the same uniform positive height
floor as the full actual Ford region. -/
theorem triangleClosedRegion_im_lower_bound {z : ℂ} (hz : z ∈ triangleClosedRegion) :
    stripRight ≤ z.im :=
  fordRegion_im_lower_bound ⟨z, triangleClosedRegion_im_pos hz⟩
    ((coe_mem_triangleClosedRegion_iff_halfFordRegion _).mp hz).1

theorem ofReal_not_mem_triangleClosedRegion (x : ℝ) :
    (x : ℂ) ∉ triangleClosedRegion := by
  intro hx
  have h := triangleClosedRegion_im_pos hx
  simp at h

/-- Density also holds in the actual upper-half-plane half-Ford region. -/
theorem closure_halfFordInterior : closure halfFordInterior = halfFordRegion := by
  rw [halfFordInterior_eq_preimage_triangleInterior,
    ← UpperHalfPlane.isOpenEmbedding_coe.isOpenMap.preimage_closure_eq_closure_preimage
      UpperHalfPlane.continuous_coe, closure_triangleInterior,
    ← halfFordRegion_eq_preimage_triangleClosedRegion]

end Wikipedia.HopfProblem.SpecialPeriods.Triangle
