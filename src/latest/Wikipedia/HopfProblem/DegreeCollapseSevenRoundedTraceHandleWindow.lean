import Wikipedia.HopfProblem.DegreeCollapseSevenRoundedTraceBoundaryCollarWindow
import Wikipedia.HopfProblem.DegreeCollapseSevenRoundedTraceOtherEndPieces

/-!
# The unchanged handle is exactly a smaller open four-ball

For an actual handle point, membership in the compact rounding image is
equivalent to lying in the final radial band. Removing that image and the
old cylinder therefore leaves a genuine product with an open four-ball.
-/

noncomputable section

open Function Set Metric
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery.FramedAttachingProduct.RoundedTrace

open NoExoticSixSphere GLOrthonormalization Stiefel

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M] [CompactSpace M]
  {e : EuclideanEmbedding 7 M}
  {a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f)

theorem handle_core_radicand_pos : 0 < 1 - 2 * (bump A).rOut := by
  have h := (twice_outer_lt_height A).trans (collarHeight_lt_gap A)
  nlinarith [sq_nonneg A.innerRadius]

def handleCoreRadius : ℝ := Real.sqrt (1 - 2 * (bump A).rOut)

theorem handleCoreRadius_pos : 0 < handleCoreRadius A :=
  Real.sqrt_pos.mpr (handle_core_radicand_pos A)

theorem handleCoreRadius_sq : (handleCoreRadius A) ^ 2 = 1 - 2 * (bump A).rOut :=
  Real.sq_sqrt (handle_core_radicand_pos A).le

theorem handleCoreRadius_lt_one : handleCoreRadius A < 1 := by
  nlinarith [handleCoreRadius_sq A, handleCoreRadius_pos A, (bump A).rOut_pos]

theorem innerRadius_lt_handleCoreRadius : A.innerRadius < handleCoreRadius A := by
  have h := (twice_outer_lt_height A).trans (collarHeight_lt_gap A)
  nlinarith [handleCoreRadius_sq A, handleCoreRadius_pos A, A.innerRadius_pos]

theorem handle_mem_added_iff {x : Vector 4} (hx : x ∈ closedBall (0 : Vector 4) 1)
    {v : Vector 4} (hv : v ∈ closedBall (0 : Vector 4) (UnroundedTrace.handleRadius A)) :
    A.map (x, v) ∈ A.collarSheet '' addedParameters A ↔
      -2 * (bump A).rOut ≤ ‖x‖ ^ 2 - 1 := by
  have hvA := (closedBall_subset_closedBall (UnroundedTrace.handleRadius_lt A).le) hv
  constructor
  · intro hp
    have hinner : A.innerRadius ≤ ‖x‖ := by
      by_contra hn
      apply addedImage_avoids_inner A hp
      exact ⟨(x, v), ⟨by simpa only [mem_closedBall, dist_zero_right] using
        (lt_of_not_ge hn).le, hv⟩, rfl⟩
    obtain ⟨q, hq, he⟩ := hp
    have hec : (HeightCylinder.heightCylinder e) (A.collarCoordinates (x, v)) =
        (HeightCylinder.heightCylinder e) (A.tube q.1, q.2) :=
      (A.map_eq_cylinder_collarCoordinates hx hinner hvA).symm.trans he.symm
    have ht := congrArg Prod.snd ((HeightCylinder.injective_heightCylinder e) hec)
    change ‖x‖ ^ 2 - 1 = q.2 at ht
    exact ht ▸ hq.2.1.1
  · intro ht
    have hn : ‖x‖ ≤ 1 := by simpa only [mem_closedBall, dist_zero_right] using hx
    have hinner : A.innerRadius ≤ ‖x‖ := by
      have h := (twice_outer_lt_height A).trans (collarHeight_lt_gap A)
      nlinarith [norm_nonneg x, A.innerRadius_pos]
    refine ⟨((SphereRadialRetraction.retract (pole 3) x, v), ‖x‖ ^ 2 - 1), ?_, ?_⟩
    · refine ⟨(closedBall_subset_closedBall (outerRadius_gt_handle A).le) hv,
        ⟨ht, by nlinarith [norm_nonneg x]⟩, ?_⟩
      exact GeneralRoundedHandleCorner.nonneg_of_corner (bump A)
        (UnroundedTrace.handleRadius_pos A).le (Or.inr hv)
    · exact (A.map_eq_cylinder_collarCoordinates hx hinner hvA).symm

theorem mem_unchangedHandleWindow_iff (p : HandleSuperlevel A) :
    p ∈ unchangedHandleWindow A ↔ p.val.1 ∈ ball (0 : Vector 4) (handleCoreRadius A) := by
  have hv := handleSuperlevel_transverse A p
  have hvA := handleSuperlevel_vector_mem A p
  have hR := handleCoreRadius_sq A
  have hRpos := handleCoreRadius_pos A
  constructor
  · intro hp
    have ht : ‖p.val.1‖ ^ 2 - 1 < -2 * (bump A).rOut := by
      apply lt_of_not_ge
      intro h
      exact hp.2 (Or.inr ((handle_mem_added_iff A (ball_subset_closedBall hp.1) hv).mpr h))
    rw [mem_ball, dist_zero_right]
    nlinarith [norm_nonneg p.val.1]
  · intro hp
    have hn : ‖p.val.1‖ < handleCoreRadius A := by
      simpa only [mem_ball, dist_zero_right] using hp
    have hx : p.val.1 ∈ ball (0 : Vector 4) 1 :=
      (ball_subset_ball (handleCoreRadius_lt_one A).le) hp
    refine ⟨hx, ?_⟩
    rintro (⟨q, hq⟩ | ha)
    · obtain ⟨s, hs, _, _⟩ := (UnroundedTrace.intersection_iff A
        (ball_subset_closedBall hx) hvA q.1 q.2.property).mp hq.symm
      have hxnorm : ‖p.val.1‖ < 1 := by simpa only [mem_ball, dist_zero_right] using hx
      rw [← hs, ClosedHemisphere.unit_norm] at hxnorm
      exact (lt_irrefl 1) hxnorm
    · have ht := (handle_mem_added_iff A (ball_subset_closedBall hx) hv).mp ha
      nlinarith [norm_nonneg p.val.1]

end Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery.FramedAttachingProduct.RoundedTrace
