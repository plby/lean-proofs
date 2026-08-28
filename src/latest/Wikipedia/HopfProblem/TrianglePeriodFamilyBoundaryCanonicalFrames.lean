import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryCanonicalFramesPositive
import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryCanonicalFramesSections
import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryCircleSlits

/-!
# The actual two boundary-column frames in the slit cover

Use the literal phases of the positive boundary circles. At one quarter
and three quarters the actual lifted curve is compared with the upper-slit
section over its actual projected overlap point. Both columns have the
same inverse-generator frame. The comparison is proved from actual path
values and covering uniqueness, not merely from component or monodromy
labels.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary

open SpecialPeriods SpecialPeriods.Triangle Meridians Homology
open BoundaryCircleSlits BoundaryLoopSquares

/-- The quarter-time overlap component: middle for zero, right for one. -/
def canonicalQuarterOverlapIndex (b : Bool) : Fin 3 := if b then 2 else 1

/-- The three-quarter-time component: left for zero, middle for one. -/
def canonicalThreeQuarterOverlapIndex (b : Bool) : Fin 3 := if b then 1 else 0

/-- The actual canonical overlap point reached at the first column time. -/
def canonicalQuarterOverlapPoint :
    (b : Bool) → overlapBase (canonicalQuarterOverlapIndex b)
  | false => middleOverlapPoint
  | true => meridianRightOverlapPoint

/-- The actual canonical overlap point reached at the second column time. -/
def canonicalThreeQuarterOverlapPoint :
    (b : Bool) → overlapBase (canonicalThreeQuarterOverlapIndex b)
  | false => meridianLeftOverlapPoint
  | true => middleOverlapPoint

@[simp] theorem canonicalQuarterOverlapPoint_false :
    canonicalQuarterOverlapPoint false = middleOverlapPoint := rfl

@[simp] theorem canonicalQuarterOverlapPoint_true :
    canonicalQuarterOverlapPoint true = meridianRightOverlapPoint := rfl

@[simp] theorem canonicalThreeQuarterOverlapPoint_false :
    canonicalThreeQuarterOverlapPoint false = meridianLeftOverlapPoint := rfl

@[simp] theorem canonicalThreeQuarterOverlapPoint_true :
    canonicalThreeQuarterOverlapPoint true = middleOverlapPoint := rfl

/-- The positive real lift at half time retains the reflected-zero endpoint. -/
theorem canonicalPositiveLift_false_half :
    canonicalPositiveLift false (1 / 2) =
      triangleGenerator₁⁻¹ • normalizedRegularMeridianLeftPoint :=
  (canonicalPositiveLift_unit false canonicalHalfTime).trans compatibleMeridianLift_false_half

/-- The positive real lift at half time retains the lifted-one endpoint. -/
theorem canonicalPositiveLift_true_half :
    canonicalPositiveLift true (1 / 2) = normalizedRegularMeridianRightPoint :=
  (canonicalPositiveLift_unit true canonicalHalfTime).trans compatibleMeridianLift_true_half

/-- The actual positive lift with exactly the phase used by the boundary-circle cover. -/
def canonicalPhasedLift (b : Bool) : C(ℝ, TriangleRegularPoint) :=
  canonicalPositivePhaseLift b (circlePhase b)

@[simp] theorem canonicalPhasedLift_apply (b : Bool) (t : ℝ) :
    canonicalPhasedLift b t = canonicalPositiveLift b (t + circlePhase b) := rfl

theorem canonicalPhasedLift_projection (b : Bool) (t : ℝ) :
    triangleRegularProject (canonicalPhasedLift b t) =
      loopPeriodic (compatibleRegularMeridian b) (t + circlePhase b) :=
  canonicalPositivePhaseLift_projection b (circlePhase b) t

theorem canonicalPhasedLift_translate (b : Bool) (k : ℤ) (t : ℝ) :
    canonicalPhasedLift b (t + k) =
      (compatibleMeridianGenerator b ^ (-k)) • canonicalPhasedLift b t :=
  canonicalPositivePhaseLift_translate b (circlePhase b) k t

/-- At quarter time both punctures have the same inverse-generator frame over the upper section. -/
theorem canonicalPhasedLift_quarter_frame (b : Bool) :
    canonicalPhasedLift b (1 / 4) = (compatibleMeridianGenerator b)⁻¹ •
      upperLiftOnOverlap normalizedSlitBaseLift (canonicalQuarterOverlapIndex b)
        (canonicalQuarterOverlapPoint b) := by
  cases b
  · change canonicalPositiveLift false ((1 / 4 : ℝ) + 3 / 4) =
      triangleGenerator₁⁻¹ • upperLiftOnOverlap normalizedSlitBaseLift 1 middleOverlapPoint
    rw [show (1 / 4 : ℝ) + 3 / 4 = 1 by norm_num]
    simp only [canonicalPositiveLift_one, compatibleMeridianGenerator,
      upperLift_middleOverlapPoint, normalizedSlitBaseLift_val]
  · change canonicalPositiveLift true ((1 / 4 : ℝ) + 1 / 4) =
      triangleGenerator₂⁻¹ • upperLiftOnOverlap normalizedSlitBaseLift 2 meridianRightOverlapPoint
    rw [show (1 / 4 : ℝ) + 1 / 4 = 1 / 2 by norm_num,
      canonicalPositiveLift_true_half, canonicalUpperRight, inv_smul_smul]

/-- At three-quarter time the same inverse-generator frame occurs in the other component. -/
theorem canonicalPhasedLift_threeQuarter_frame (b : Bool) :
    canonicalPhasedLift b (3 / 4) = (compatibleMeridianGenerator b)⁻¹ •
      upperLiftOnOverlap normalizedSlitBaseLift (canonicalThreeQuarterOverlapIndex b)
        (canonicalThreeQuarterOverlapPoint b) := by
  cases b
  · change canonicalPositiveLift false ((3 / 4 : ℝ) + 3 / 4) =
      triangleGenerator₁⁻¹ • upperLiftOnOverlap normalizedSlitBaseLift 0 meridianLeftOverlapPoint
    rw [show (3 / 4 : ℝ) + 3 / 4 = (1 / 2 : ℝ) + 1 by norm_num, canonicalUpperLeft]
    simpa only [Int.cast_one, zpow_neg_one, compatibleMeridianGenerator,
      canonicalPositiveLift_false_half] using canonicalPositiveLift_translate false 1 (1 / 2)
  · change canonicalPositiveLift true ((3 / 4 : ℝ) + 1 / 4) =
      triangleGenerator₂⁻¹ • upperLiftOnOverlap normalizedSlitBaseLift 1 middleOverlapPoint
    rw [show (3 / 4 : ℝ) + 1 / 4 = 1 by norm_num]
    simp only [canonicalPositiveLift_one, compatibleMeridianGenerator,
      upperLift_middleOverlapPoint, normalizedSlitBaseLift_val]

/-- The first frame theorem identifies the actual projected point, not only its component. -/
theorem canonicalPhasedLift_quarter_project (b : Bool) :
    triangleRegularProject (canonicalPhasedLift b (1 / 4)) =
      (canonicalQuarterOverlapPoint b).val := by
  rw [canonicalPhasedLift_quarter_frame, triangleRegularProject_covering.map_smul,
    upperLiftOnOverlap_project]

/-- The second frame theorem likewise retains the exact actual overlap point. -/
theorem canonicalPhasedLift_threeQuarter_project (b : Bool) :
    triangleRegularProject (canonicalPhasedLift b (3 / 4)) =
      (canonicalThreeQuarterOverlapPoint b).val := by
  rw [canonicalPhasedLift_threeQuarter_frame, triangleRegularProject_covering.map_smul,
    upperLiftOnOverlap_project]

end Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary
