import Wikipedia.HopfProblem.TriangleUniformizationGluingSignedHalfPlane
import Wikipedia.HopfProblem.RiemannSphereMobiusClosedDiscAnalytic
import Mathlib.Topology.Maps.Proper.Basic

/-!
# Finite triangle homeomorphisms supply the actual gluing data

A homeomorphism from the literal closed half-Ford region to an oriented
closed half-plane supplies the continuous boundary map used in reflection
gluing. Its orientation is normalized to a sign without changing the map
or its marked values. Properness follows from the actual homeomorphism
and the closed inclusion into the complex plane.
-/

noncomputable section

open Set UpperHalfPlane Complex
open scoped Topology

namespace Wikipedia.HopfProblem.TriangleUniformizationGluing

open SpecialPeriods.Triangle RiemannSphere

def halfPlaneOrientationSign (k : ℝ) : ℝ := if 0 < k then 1 else -1

theorem halfPlaneOrientationSign_sq (k : ℝ) : halfPlaneOrientationSign k ^ 2 = 1 := by
  unfold halfPlaneOrientationSign
  split_ifs <;> norm_num

theorem halfPlaneOrientationSign_nonneg_iff {k : ℝ} (hk : k ≠ 0) (t : ℝ) :
    0 ≤ halfPlaneOrientationSign k * t ↔ 0 ≤ k * t := by
  unfold halfPlaneOrientationSign
  split_ifs with hp
  · simpa only [one_mul] using (mul_nonneg_iff_of_pos_left hp).symm
  · have hn : k < 0 := lt_of_le_of_ne (le_of_not_gt hp) hk
    simp only [neg_one_mul, neg_nonneg]
    constructor
    · exact fun ht => mul_nonneg_of_nonpos_of_nonpos hn.le ht
    · intro ht
      by_contra h
      exact (not_le_of_gt (mul_neg_of_neg_of_pos hn (lt_of_not_ge h))) ht

theorem halfPlaneOrientationSign_pos_iff {k : ℝ} (hk : k ≠ 0) (t : ℝ) :
    0 < halfPlaneOrientationSign k * t ↔ 0 < k * t := by
  unfold halfPlaneOrientationSign
  split_ifs with hp
  · simpa only [one_mul] using (mul_pos_iff_of_pos_left hp).symm
  · have hn : k < 0 := lt_of_le_of_ne (le_of_not_gt hp) hk
    simp only [neg_one_mul, neg_pos]
    constructor
    · exact fun ht => mul_pos_of_neg_of_neg hn ht
    · intro ht
      by_contra h
      exact (not_lt_of_ge (mul_nonpos_of_nonpos_of_nonneg hn.le (le_of_not_gt h))) ht

/-- The extension is only read on the half-Ford region in the gluing data. -/
def halfFordHomeomorphExtension {k : ℝ}
    (e : halfFordRegion ≃ₜ closedOrientedHalfPlane k) (z : ℍ) : ℂ := by
  classical
  exact if hz : z ∈ halfFordRegion then (e ⟨z, hz⟩ : ℂ) else 0

@[simp] theorem halfFordHomeomorphExtension_coe {k : ℝ}
    (e : halfFordRegion ≃ₜ closedOrientedHalfPlane k) (z : halfFordRegion) :
    halfFordHomeomorphExtension e z = (e z : ℂ) := by
  simp only [halfFordHomeomorphExtension, dif_pos z.property]

theorem halfFordHomeomorphExtension_of_mem {k : ℝ}
    (e : halfFordRegion ≃ₜ closedOrientedHalfPlane k)
    {z : ℍ} (hz : z ∈ halfFordRegion) :
    halfFordHomeomorphExtension e z = (e ⟨z, hz⟩ : ℂ) :=
  halfFordHomeomorphExtension_coe e ⟨z, hz⟩

theorem halfFordHomeomorphExtension_continuousOn {k : ℝ}
    (e : halfFordRegion ≃ₜ closedOrientedHalfPlane k) :
    ContinuousOn (halfFordHomeomorphExtension e) halfFordRegion := by
  rw [continuousOn_iff_continuous_domRestrict]
  change Continuous (fun z : halfFordRegion => halfFordHomeomorphExtension e z)
  simp only [halfFordHomeomorphExtension_coe]
  exact continuous_subtype_val.comp e.continuous

theorem halfFordHomeomorphExtension_isProperMap {k : ℝ}
    (e : halfFordRegion ≃ₜ closedOrientedHalfPlane k) :
    IsProperMap (fun z : halfFordRegion => halfFordHomeomorphExtension e z) := by
  have hc : IsClosed (closedOrientedHalfPlane k) :=
    isClosed_le continuous_const (continuous_const.mul Complex.continuous_im)
  simpa only [Function.comp_def, halfFordHomeomorphExtension_coe] using
    hc.isProperMap_subtypeVal.comp e.isProperMap

/-- A genuine finite-half homeomorphism and its interior correspondence
give all signed half-plane gluing fields, including real boundary values. -/
def signedHalfPlaneMapOfHomeomorph {k : ℝ} (hk : k ≠ 0)
    (e : halfFordRegion ≃ₜ closedOrientedHalfPlane k)
    (hinterior : ∀ z : halfFordRegion,
      0 < k * (e z : ℂ).im ↔ (z : ℍ) ∈ halfFordInterior) : SignedHalfPlaneMap where
  toFun := halfFordHomeomorphExtension e
  continuousOn := halfFordHomeomorphExtension_continuousOn e
  boundary_real := by
    intro z hz hi
    rw [halfFordHomeomorphExtension_of_mem e hz]
    have hn : ¬ 0 < k * (e ⟨z, hz⟩ : ℂ).im := fun h => hi ((hinterior ⟨z, hz⟩).mp h)
    have he : k * (e ⟨z, hz⟩ : ℂ).im = 0 :=
      le_antisymm (le_of_not_gt hn) (e ⟨z, hz⟩).property
    exact (mul_eq_zero.mp he).resolve_left hk
  orientation := halfPlaneOrientationSign k
  orientation_sq := halfPlaneOrientationSign_sq k
  injOn := by
    intro z hz w hw he
    rw [halfFordHomeomorphExtension_of_mem e hz,
      halfFordHomeomorphExtension_of_mem e hw] at he
    exact congrArg Subtype.val (e.injective (Subtype.ext he))
  image_eq := by
    ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      rw [mem_ofPred_eq, halfFordHomeomorphExtension_of_mem e hz,
        halfPlaneOrientationSign_nonneg_iff hk]
      exact (e ⟨z, hz⟩).property
    · intro hw
      have hwk : w ∈ closedOrientedHalfPlane k :=
        (halfPlaneOrientationSign_nonneg_iff hk w.im).mp hw
      obtain ⟨z, hz⟩ := e.surjective ⟨w, hwk⟩
      refine ⟨z, z.property, ?_⟩
      rw [halfFordHomeomorphExtension_coe]
      exact congrArg Subtype.val hz
  interior_positive := by
    intro z hz
    have hzR : z ∈ halfFordRegion := halfFordInterior_subset_halfFordRegion hz
    rw [halfFordHomeomorphExtension_of_mem e hzR,
      halfPlaneOrientationSign_pos_iff hk]
    exact (hinterior ⟨z, hzR⟩).mpr hz

@[simp] theorem signedHalfPlaneMapOfHomeomorph_apply {k : ℝ} (hk : k ≠ 0)
    (e : halfFordRegion ≃ₜ closedOrientedHalfPlane k)
    (hinterior : ∀ z : halfFordRegion,
      0 < k * (e z : ℂ).im ↔ (z : ℍ) ∈ halfFordInterior) (z : halfFordRegion) :
    signedHalfPlaneMapOfHomeomorph hk e hinterior z = (e z : ℂ) :=
  halfFordHomeomorphExtension_coe e z

end Wikipedia.HopfProblem.TriangleUniformizationGluing
