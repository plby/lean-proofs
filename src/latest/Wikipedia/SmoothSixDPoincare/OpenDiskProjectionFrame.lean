import Wikipedia.SmoothSixDPoincare.StarConvexProjectionFrame
import Mathlib.Analysis.Normed.Module.Ball.Pointwise

/-!
# Projection frames valid throughout an open disk neighborhood

An open neighborhood of a compact closed ball contains a slightly larger
closed ball. Applying radial transport on that larger ball gives a frame
whose injectivity and range equations hold on an actual open neighborhood
of the original disk, not only at its closed-disk points.
-/

noncomputable section

open Set
open scoped ContDiff Topology

namespace Wikipedia.SmoothSixDPoincare.DiskFraming

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- A smooth projection near the closed disk has a genuine frame on an open neighborhood. -/
theorem exists_smooth_frame_on_neighborhood_closedBall {U : Set E} (hU : IsOpen U)
    (hballU : Metric.closedBall (0 : E) 1 ⊆ U) (P : E → F →L[ℝ] F)
    (hP : ∀ x ∈ U, IsIdempotentElem (P x)) (hs : ContDiffOn ℝ ∞ P U) :
    ∃ V : Set E, IsOpen V ∧ Metric.closedBall (0 : E) 1 ⊆ V ∧ V ⊆ U ∧
      ∃ A : E → (P 0).range →L[ℝ] F, ContDiffOn ℝ ∞ A V ∧
        ∀ x ∈ V, Function.Injective (A x) ∧ (A x).range = (P x).range := by
  obtain ⟨δ, hδ, hthick⟩ :=
    (isCompact_closedBall (0 : E) 1).exists_cthickening_subset_open hU hballU
  have hbU : Metric.closedBall (0 : E) (δ + 1) ⊆ U := by
    simpa only [cthickening_closedBall hδ.le zero_le_one] using hthick
  have hr : 1 < δ + 1 := by linarith
  obtain ⟨W, hW, hbW, A, hA, hArange⟩ := exists_smooth_frame_near_starConvex
    (isCompact_closedBall (0 : E) (δ + 1))
    ((convex_closedBall (0 : E) (δ + 1)).starConvex
      (Metric.mem_closedBall_self (by linarith)))
    hU hbU P (fun x hx => hP x (hbU hx)) hs
  refine ⟨W ∩ Metric.ball 0 (δ + 1), hW.inter Metric.isOpen_ball, ?_, ?_, A,
    hA.mono inter_subset_left, ?_⟩
  · intro x hx
    exact ⟨hbW (Metric.closedBall_subset_closedBall hr.le hx),
      Metric.closedBall_subset_ball hr hx⟩
  · exact fun _ hx => hbU (Metric.ball_subset_closedBall hx.2)
  · exact fun x hx => hArange x (Metric.ball_subset_closedBall hx.2)

end Wikipedia.SmoothSixDPoincare.DiskFraming
