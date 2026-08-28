import Wikipedia.NoExoticSixSphere.PartialGradientRadial

/-!
# Fiber-radius control for center-preserving perturbations

A perturbation with the same center changes the fiber radius by at most its
ambient distance. Subsequent radial expansion never decreases that radius.
These estimates prevent points initially away from a fiber core from entering
a smaller core during the two stages.
-/

open Set unitInterval

namespace NoExoticSixSphere.PartialGradientCoordinates.LocalData

variable {D E : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {f : E → ℝ} {L : D →L[ℝ] E} {U : Set E} (C : LocalData f L U)

theorem fiber_norm_sub_dist_le {z z' : E} (hc : C.center z' = C.center z) :
    ‖z - C.center z‖ - dist z' z ≤ ‖z' - C.center z'‖ := by
  have hh := norm_sub_norm_le (z - C.center z) (z' - C.center z')
  have he : (z - C.center z) - (z' - C.center z') = z - z' := by rw [hc]; abel
  rw [he, ← dist_eq_norm z z', dist_comm z z'] at hh
  linarith

theorem fiber_norm_gt_of_dist_lt {z z' : E} (hc : C.center z' = C.center z)
    {ε : ℝ} (hclose : dist z' z < ε) :
    ‖z - C.center z‖ - ε < ‖z' - C.center z'‖ := by
  have hh := C.fiber_norm_sub_dist_le hc
  linarith

theorem radial_fiber_norm_ge (r : ℝ) {z : E} (hz : z ∈ C.radialDomain r) (s : I) :
    ‖z - C.center z‖ ≤ ‖C.radial r (s, z) - C.center (C.radial r (s, z))‖ := by
  rw [C.center_radial r hz s]
  simpa only [radial, add_sub_cancel_left] using
    (RadialExpansion.norm_expand_bounds r hz.2.2.1 hz.2.2.2 s).1

theorem radial_fiber_norm_gt_of_close (r : ℝ) {z z' : E} (hz' : z' ∈ C.radialDomain r)
    (hc : C.center z' = C.center z) {ε : ℝ} (hclose : dist z' z < ε) (s : I) :
    ‖z - C.center z‖ - ε < ‖C.radial r (s, z') - C.center (C.radial r (s, z'))‖ :=
  (C.fiber_norm_gt_of_dist_lt hc hclose).trans_le (C.radial_fiber_norm_ge r hz' s)

end NoExoticSixSphere.PartialGradientCoordinates.LocalData
