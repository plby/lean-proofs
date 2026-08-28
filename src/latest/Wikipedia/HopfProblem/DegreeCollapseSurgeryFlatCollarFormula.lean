import Wikipedia.HopfProblem.DegreeCollapseSurgeryFlatTargetPieces

/-!
# The canonical flat collar has the rounding retraction's exact endpoint

On the negative side the canonical radial exchange is the actual retained
handle collar, including its original sphere direction and signed height.
On the nonnegative side the map is the old tube at height zero. Together
these are precisely the piecewise endpoint of the checked rounding motion.
-/

noncomputable section

open Set Function Metric Topology
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.TraceBody

open NoExoticSixSphere NoExoticSixSphere.GLOrthonormalization NoExoticSixSphere.Stiefel
open EuclideanEmbedding
open EuclideanEmbedding.FramedAttachingProduct
open EuclideanEmbedding.FramedAttachingProduct.RoundedTrace

variable {M : Type} [TopologicalSpace M] [ChartedSpace (Vector 6) M] [CompactSpace M]
  [T2Space M] {e : EuclideanEmbedding 6 M}
  {a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f) (hR : A.radius = 2)

include hR in
theorem flat_collar_handle_map (p : boundaryCollarParameters A) (hu : p.val.2.2 < 0) :
    A.map (Real.sqrt (1 + p.val.2.2) • p.val.1.val, p.val.2.1.val) =
      A.collarSheet ((p.val.1, p.val.2.1.val), p.val.2.2) := by
  let r := Real.sqrt (1 + p.val.2.2)
  let x : Vector 4 := r • p.val.1.val
  have hr : 0 < r := Real.sqrt_pos.mpr
    (by linarith [UnitSurgery.collar_parameter_gt_neg_one A p])
  have hs : r ^ 2 = 1 + p.val.2.2 :=
    Real.sq_sqrt (by linarith [UnitSurgery.collar_parameter_gt_neg_one A p])
  have hn : ‖x‖ = r := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr, ClosedHemisphere.unit_norm, mul_one]
  have hx : x ∈ closedBall (0 : Vector 4) 1 := by
    rw [mem_closedBall_zero_iff, hn]
    nlinarith
  have hi : A.innerRadius ≤ ‖x‖ := by
    rw [hn]
    have hp := (mem_boundaryCollarParameters_iff_interval A p.val).mp p.property
    have hb := collarHeight_lt_gap A
    nlinarith [A.innerRadius_pos, hp.1]
  have hv : p.val.2.1.val ∈ closedBall (0 : Vector 3) A.radius :=
    (closedBall_subset_closedBall (by rw [hR]; norm_num : (1 : ℝ) ≤ A.radius))
      (sphere_subset_closedBall p.val.2.1.property)
  have hne : x ≠ 0 := norm_pos_iff.mp (hn ▸ hr)
  have hd : SphereRadialRetraction.retract (pole 3) x = p.val.1 := by
    apply Subtype.ext
    rw [SphereRadialRetraction.retract, dif_neg hne]
    change NormedSpace.normalize (r • p.val.1.val) = p.val.1.val
    rw [NormedSpace.normalize_smul_of_pos hr]
    exact NormedSpace.normalize_eq_self_of_norm_eq_one (ClosedHemisphere.unit_norm p.val.1)
  have ht : ‖x‖ ^ 2 - 1 = p.val.2.2 := by rw [hn, hs]; ring
  change A.map (x, p.val.2.1.val) = _
  rw [A.map_eq_cylinder_collarCoordinates hx hi hv, A.collarCoordinates_apply, hd]
  change e.heightCylinder (A.tube (p.val.1, p.val.2.1.val), ‖x‖ ^ 2 - 1) =
    e.heightCylinder (A.tube (p.val.1, p.val.2.1.val), p.val.2.2)
  rw [ht]

theorem flatTarget_collar (p : boundaryCollarParameters A) :
    (flatTargetInclusion A hR (UnitSurgery.collarMap A hR p)).val =
      A.collarSheet ((p.val.1,
        Real.sqrt ((UnroundedTrace.handleRadius A) ^ 2 + max p.val.2.2 0) • p.val.2.1.val),
        min p.val.2.2 0) := by
  by_cases hu : 0 ≤ p.val.2.2
  · rw [flatTarget_collar_nonneg A hR p hu]
    rw [TraceCoreAttachment.handleRadius_eq_one A hR, one_pow,
      max_eq_left hu, min_eq_right hu]
    rfl
  · have hn := lt_of_not_ge hu
    rw [flatTarget_collar_neg A hR p hn, flat_collar_handle_map A hR p hn]
    rw [TraceCoreAttachment.handleRadius_eq_one A hR, one_pow,
      max_eq_right hn.le, min_eq_left hn.le, add_zero, Real.sqrt_one, one_smul]

end Wikipedia.HopfProblem.DegreeCollapse.TraceBody
