import Wikipedia.NoExoticSixSphere.SphereSumSourceCover
import Wikipedia.NoExoticSixSphere.SphereSumCapCoordinates
import Wikipedia.NoExoticSixSphere.SphereSumCapProfile

/-! # Exact separation of finite neck coordinates from the exterior caps -/

noncomputable section

open Set Function Metric Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.SphereSumNeck

open GLOrthonormalization

theorem capProfile_lt_four (a : ℝ) {t : ℝ} (ht : t < 4) : capProfile a t < 4 := by
  by_cases hsmall : t ≤ 2
  · linarith [capProfile_le_two a hsmall]
  · rw [capProfile_eq_id a t (le_of_lt (lt_of_not_ge hsmall))]
    exact ht

theorem point_mem_neckRegion (q : ℝ × Sphere 2) (hq : q.1 ∈ Ioo (-4 : ℝ) 4) :
    SphereCylinder.point 2 q ∈ neckRegion := by
  have hn : 0 < ‖SphereCylinder.vector 2 q‖⁻¹ :=
    inv_pos.mpr (norm_pos_iff.mpr (SphereCylinder.vector_ne_zero 2 q))
  have ht : |q.1| < 4 := abs_lt.mpr hq
  change |(SphereCylinder.point 2 q).val 0| <
    4 * ‖SphereCylinder.tail 2 (SphereCylinder.point 2 q).val‖
  rw [SphereCylinder.point_head, SphereCylinder.norm_tail_point,
    abs_mul, abs_of_pos hn]
  simpa only [mul_comm] using mul_lt_mul_of_pos_left ht hn

theorem reflectHead_mem_neckRegion_iff (x : Sphere 3) :
    reflectHead x ∈ neckRegion ↔ x ∈ neckRegion := by
  change |(reflectHead x).val 0| < 4 * ‖SphereCylinder.tail 2 (reflectHead x).val‖ ↔ _
  rw [reflectHead_head, reflectHead_tail, abs_neg]
  rfl

theorem point_head_pos {t : ℝ} (ht : 0 < t) (s : Sphere 2) :
    0 < (SphereCylinder.point 2 (t, s)).val 0 := by
  rw [SphereCylinder.point_head]
  exact mul_pos (inv_pos.mpr (norm_pos_iff.mpr (SphereCylinder.vector_ne_zero 2 (t, s)))) ht

theorem sphereCap_eq_sourceChart_ray {ε t : ℝ} (hε : 0 < ε) (ht : 0 < t)
    (s : Sphere 2) {x : Sphere 3} (hx : 0 < x.val 0) :
    sphereCap ε x = sourceChart ((ε * t) • s.val) ↔ x = SphereCylinder.point 2 (t, s) := by
  constructor
  · intro he
    exact sphereCap_injOn hε.ne' hx (point_head_pos ht s)
      (he.trans (sphereCap_cylinder hε t s ht).symm)
  · rintro rfl
    exact sphereCap_cylinder hε t s ht

theorem sphereCap_ray_implies_neckRegion {ε t : ℝ} (hε : 0 < ε) (ht : 0 < t)
    (ht4 : t < 4) (s : Sphere 2) {x : Sphere 3} (hx : 0 < x.val 0)
    (he : sphereCap ε x = sourceChart ((ε * t) • s.val)) : x ∈ neckRegion := by
  rw [(sphereCap_eq_sourceChart_ray hε ht s hx).mp he]
  exact point_mem_neckRegion (t, s) ⟨by linarith, ht4⟩

end NoExoticSixSphere.SphereSumNeck
