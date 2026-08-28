import Wikipedia.HopfProblem.DegreeCollapseLowAttachingRoundingData
import Wikipedia.HopfProblem.DegreeCollapseLowNormalizedFramedAttachingProduct

/-!

# Constructed margins for a direct native surgery boundary pair

Choose the old closed face outside the entire added rounding region. The
inner cap cut lies in the original disk collar and strictly in the unchanged
left branch of the rounding graph. Radius-two normalization is already
constructed; it makes the handle transverse radius one.
-/

noncomputable section

open Function Set Metric
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.LowSurgery.FramedAttachingProduct.SurgeryPair

open NoExoticSixSphere GLOrthonormalization Stiefel RoundedTrace

variable {d : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M]
  [CompactSpace M] {e : EuclideanEmbedding 7 M}
  {a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel}
  {f : NoExoticSixSphere.Sphere d → M} (A : FramedAttachingProduct e a f)

omit [CompactSpace M] in
theorem handleRadius_eq_one (hR : A.radius = 2) : UnroundedTrace.handleRadius A = 1 := by
  rw [UnroundedTrace.handleRadius, hR]
  norm_num

theorem three_outer_lt_height : 3 * (bump A).rOut < collarHeight A := by
  have h := min_le_left (collarHeight A) (radialGap A)
  change scale A ≤ collarHeight A at h
  change 3 * (scale A / 4) < collarHeight A
  linarith [scale_pos A]

def oldRadius : ℝ := (outerRadius A + A.radius) / 2

theorem oldRadius_gt_outer : outerRadius A < oldRadius A := by
  dsimp only [oldRadius]
  linarith [outerRadius_lt A]

theorem oldRadius_lt : oldRadius A < A.radius := by
  dsimp only [oldRadius]
  linarith [outerRadius_lt A]

theorem oldRadius_pos : 0 < oldRadius A :=
  (outerRadius_nonneg A).trans_lt (oldRadius_gt_outer A)

theorem oldRadius_gt_one (hR : A.radius = 2) : 1 < oldRadius A := by
  have h := outerRadius_gt_handle A
  rw [handleRadius_eq_one A hR] at h
  exact h.trans (oldRadius_gt_outer A)

def cutRadius : ℝ := Real.sqrt (1 - 3 * (bump A).rOut)

theorem cutRadicand_pos : 0 < 1 - 3 * (bump A).rOut := by
  have h := three_outer_lt_height A
  have hg := collarHeight_lt_gap A
  nlinarith [sq_nonneg A.innerRadius]

theorem cutRadius_pos : 0 < cutRadius A := Real.sqrt_pos.mpr (cutRadicand_pos A)

theorem cutRadius_sq : (cutRadius A) ^ 2 = 1 - 3 * (bump A).rOut :=
  Real.sq_sqrt (cutRadicand_pos A).le

theorem cutRadius_lt_one : cutRadius A < 1 := by
  nlinarith [cutRadius_sq A, cutRadius_pos A, (bump A).rOut_pos]

theorem innerRadius_lt_cutRadius : A.innerRadius < cutRadius A := by
  have h := three_outer_lt_height A
  have hg := collarHeight_lt_gap A
  nlinarith [cutRadius_sq A, cutRadius_pos A, A.innerRadius_pos]

theorem cutParameter_gt_neg_height : -collarHeight A < (cutRadius A) ^ 2 - 1 := by
  rw [cutRadius_sq]
  linarith [three_outer_lt_height A]

theorem cutParameter_lt_neg_twice_outer :
    (cutRadius A) ^ 2 - 1 < -2 * (bump A).rOut := by
  rw [cutRadius_sq]
  linarith [(bump A).rOut_pos]

theorem oldParameter_gt_twice_outer (hR : A.radius = 2) :
    2 * (bump A).rOut < (oldRadius A) ^ 2 - 1 := by
  have hs := outerRadius_sq A
  rw [handleRadius_eq_one A hR] at hs
  nlinarith [oldRadius_gt_outer A, oldRadius_pos A, outerRadius_nonneg A]

theorem oldParameter_lt_gap (hR : A.radius = 2) :
    (oldRadius A) ^ 2 - 1 < radialGap A := by
  change (oldRadius A) ^ 2 - 1 < A.radius ^ 2 - (UnroundedTrace.handleRadius A) ^ 2
  rw [handleRadius_eq_one A hR]
  nlinarith [oldRadius_lt A, oldRadius_pos A, A.radius_pos]

end Wikipedia.HopfProblem.DegreeCollapse.LowSurgery.FramedAttachingProduct.SurgeryPair
