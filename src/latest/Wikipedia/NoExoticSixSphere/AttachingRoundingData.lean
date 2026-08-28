import Wikipedia.NoExoticSixSphere.UnroundedCornerModel
import Wikipedia.NoExoticSixSphere.RoundedHandleCorner

/-!
# Constructed rounding parameters within the actual attaching collar

No cutoff size or collar band is an extra input. The proved uniform corner
band and the retained transverse margin determine a smooth rounding bump.
Its entire possible added region fits strictly inside both margins.
-/

noncomputable section

open Function Set Metric
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.RoundedTrace

open GLOrthonormalization Stiefel

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector n) M]
  {e : EuclideanEmbedding n M}
  {a : SmoothRangeFrame (𝓡 n) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f)

def collarHeight : ℝ := Classical.choose A.exists_cornerHeightBand

theorem collarHeight_pos : 0 < collarHeight A := (Classical.choose_spec A.exists_cornerHeightBand).1

theorem collarHeight_lt_height : collarHeight A < UnroundedTrace.height A :=
  (Classical.choose_spec A.exists_cornerHeightBand).2.1

theorem collarHeight_lt_gap : collarHeight A < 1 - A.innerRadius ^ 2 :=
  (Classical.choose_spec A.exists_cornerHeightBand).2.2.1

theorem sheet_mem_unrounded_iff (s : Sphere 3) {v : Vector (n - 3)}
    (hv : v ∈ ball (0 : Vector (n - 3)) A.radius) {t : ℝ} (ht : ‖t‖ ≤ collarHeight A) :
    A.collarSheet ((s, v), t) ∈ UnroundedTrace.ambientSet A ↔
      0 ≤ t ∨ v ∈ closedBall (0 : Vector (n - 3)) (UnroundedTrace.handleRadius A) :=
  (Classical.choose_spec A.exists_cornerHeightBand).2.2.2 s v hv t ht

def radialGap : ℝ := A.radius ^ 2 - (UnroundedTrace.handleRadius A) ^ 2

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

theorem mem_outerBall {v : Vector (n - 3)}
    (hv : ‖v‖ ^ 2 ≤ (UnroundedTrace.handleRadius A) ^ 2 + 2 * (bump A).rOut) :
    v ∈ closedBall (0 : Vector (n - 3)) (outerRadius A) := by
  rw [mem_closedBall, dist_zero_right]
  nlinarith [outerRadius_sq A, outerRadius_nonneg A, norm_nonneg v]

end NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.RoundedTrace
