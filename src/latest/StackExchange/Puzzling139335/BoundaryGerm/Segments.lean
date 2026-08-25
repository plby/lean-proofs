import StackExchange.Puzzling139335.BoundaryGerm
import Mathlib.Analysis.Convex.Between
import Mathlib.Analysis.Normed.Module.Ray

/-!
# Directions of equal straight boundary germs

Equality of initial segment germs determines their positive ray.  Segments
of equal length with that germ therefore have the same far endpoint.
-/

open Set

namespace Puzzling139335.SameBoundaryGerm

theorem segments_sameRay {v a b : Plane}
    (h : SameBoundaryGerm (segment ℝ v a) (segment ℝ v b) v) (ha : a ≠ v) :
    SameRay ℝ (a - v) (b - v) := by
  obtain ⟨r, hr, heq⟩ := h
  obtain ⟨z, hz, hseg⟩ := exists_initial_segment_subset_ball ha hr
  have hza : z ∈ segment ℝ v a := (hseg (right_mem_segment ℝ v z)).1
  have hzball : z ∈ Metric.ball v r := (hseg (right_mem_segment ℝ v z)).2
  have hzb : z ∈ segment ℝ v b := ((Set.ext_iff.mp heq z).mp ⟨hzball, hza⟩).2
  have hzaRay : SameRay ℝ (z - v) (a - v) :=
    (mem_segment_iff_wbtw.mp hza).sameRay_vsub_left
  have hzbRay : SameRay ℝ (z - v) (b - v) :=
    (mem_segment_iff_wbtw.mp hzb).sameRay_vsub_left
  exact hzaRay.symm.trans hzbRay (fun hzero => False.elim (hz (sub_eq_zero.mp hzero)))

theorem segment_endpoint_eq_of_dist_eq {v a b : Plane}
    (h : SameBoundaryGerm (segment ℝ v a) (segment ℝ v b) v) (ha : a ≠ v)
    (hdist : dist a v = dist b v) : a = b := by
  have hnorm : ‖a - v‖ = ‖b - v‖ := by simpa only [dist_eq_norm] using hdist
  exact sub_left_inj.mp ((h.segments_sameRay ha).eq_of_norm_eq hnorm)

theorem segments_inv_norm_smul_eq {v a b : Plane}
    (h : SameBoundaryGerm (segment ℝ v a) (segment ℝ v b) v)
    (ha : a ≠ v) (hb : b ≠ v) :
    ‖a - v‖⁻¹ • (a - v) = ‖b - v‖⁻¹ • (b - v) :=
  (h.segments_sameRay ha).inv_norm_smul_eq (sub_ne_zero.mpr ha) (sub_ne_zero.mpr hb)

end Puzzling139335.SameBoundaryGerm
