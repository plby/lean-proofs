import Wikipedia.HopfProblem.DegreeCollapseLowUnroundedCornerModel
import Wikipedia.HopfProblem.DegreeCollapseGeneralRoundedHandleCorner

/-!

# Constructed rounding parameters within the actual low-dimensional collar

The proved uniform corner band and transverse margin determine the rounding
bump. No cutoff size or collar width is supplied separately. Its entire
possible added region fits strictly inside both actual margins.
-/

noncomputable section

open Function Set Metric
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.LowSurgery.FramedAttachingProduct.RoundedTrace

open NoExoticSixSphere GLOrthonormalization Stiefel

variable {d : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M] [CompactSpace M]
  {e : EuclideanEmbedding 7 M}
  {a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel}
  {f : NoExoticSixSphere.Sphere d → M}
  (A : FramedAttachingProduct e a f)

def collarHeight : ℝ := Classical.choose A.exists_cornerHeightBand

theorem collarHeight_pos : 0 < collarHeight A := (Classical.choose_spec A.exists_cornerHeightBand).1

theorem collarHeight_lt_height : collarHeight A < UnroundedTrace.height A :=
  (Classical.choose_spec A.exists_cornerHeightBand).2.1

theorem collarHeight_lt_gap : collarHeight A < 1 - A.innerRadius ^ 2 :=
  (Classical.choose_spec A.exists_cornerHeightBand).2.2.1

theorem sheet_mem_unrounded_iff (s : NoExoticSixSphere.Sphere d) {v : Vector (7 - d)}
    (hv : v ∈ ball (0 : Vector (7 - d)) A.radius) {t : ℝ} (ht : ‖t‖ ≤ collarHeight A) :
    A.collarSheet ((s, v), t) ∈ UnroundedTrace.ambientSet A ↔
      0 ≤ t ∨ v ∈ closedBall (0 : Vector (7 - d)) (UnroundedTrace.handleRadius A) :=
  (Classical.choose_spec A.exists_cornerHeightBand).2.2.2 s v hv t ht

def radialGap : ℝ := A.radius ^ 2 - (UnroundedTrace.handleRadius A) ^ 2

omit [CompactSpace M] in
theorem radialGap_pos : 0 < radialGap A := by
  dsimp only [radialGap, UnroundedTrace.handleRadius]
  nlinarith [A.radius_pos]

def scale : ℝ := min (collarHeight A) (radialGap A)

theorem scale_pos : 0 < scale A := lt_min (collarHeight_pos A) (radialGap_pos A)

def bump : ContDiffBump (0 : ℝ) where
  rIn := scale A / 8
  rOut := scale A / 4
  rIn_pos := div_pos (scale_pos A) (by norm_num)
  rIn_lt_rOut := by linarith [scale_pos A]

theorem twice_outer_lt_height : 2 * (bump A).rOut < collarHeight A := by
  have h := min_le_left (collarHeight A) (radialGap A)
  change 2 * (scale A / 4) < collarHeight A
  change scale A ≤ collarHeight A at h
  linarith [scale_pos A]

theorem twice_outer_lt_radialGap : 2 * (bump A).rOut < radialGap A := by
  have h := min_le_right (collarHeight A) (radialGap A)
  change 2 * (scale A / 4) < radialGap A
  change scale A ≤ radialGap A at h
  linarith [scale_pos A]

def outerRadius : ℝ :=
  Real.sqrt ((UnroundedTrace.handleRadius A) ^ 2 + 2 * (bump A).rOut)

theorem outerRadius_nonneg : 0 ≤ outerRadius A := Real.sqrt_nonneg _

theorem outerRadius_sq : (outerRadius A) ^ 2 =
    (UnroundedTrace.handleRadius A) ^ 2 + 2 * (bump A).rOut :=
  Real.sq_sqrt (by nlinarith [(bump A).rOut_pos, sq_nonneg (UnroundedTrace.handleRadius A)])

theorem outerRadius_lt : outerRadius A < A.radius := by
  have hg := twice_outer_lt_radialGap A
  dsimp only [radialGap] at hg
  nlinarith [outerRadius_sq A, outerRadius_nonneg A, A.radius_pos]

theorem outerRadius_gt_handle : UnroundedTrace.handleRadius A < outerRadius A := by
  nlinarith [outerRadius_sq A, outerRadius_nonneg A, UnroundedTrace.handleRadius_pos A,
    (bump A).rOut_pos]

theorem mem_outerBall {v : Vector (7 - d)}
    (hv : ‖v‖ ^ 2 ≤ (UnroundedTrace.handleRadius A) ^ 2 + 2 * (bump A).rOut) :
    v ∈ closedBall (0 : Vector (7 - d)) (outerRadius A) := by
  rw [mem_closedBall, dist_zero_right]
  nlinarith [outerRadius_sq A, outerRadius_nonneg A, norm_nonneg v]

end Wikipedia.HopfProblem.DegreeCollapse.LowSurgery.FramedAttachingProduct.RoundedTrace
