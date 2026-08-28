import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryLiftedCurve
import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryEllipticFrames
import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryLoopSquares

/-!
# The actual periodic lift of the fixed clockwise meridians

The periodic real extension of a clockwise meridian has a unique covering
lift from the canonical regular point. On the unit interval it is the
already constructed clockwise lift. Its actual endpoint therefore fixes
the entire integer deck action, without any new orientation assumption
or change of the previously constructed elliptic frames.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary

open SpecialPeriods SpecialPeriods.Triangle Meridians BoundaryLoopSquares
open SpecialPeriods.EllipticAttachingMeridians

/-- The actual real-time covering lift of the periodic clockwise meridian. -/
def clockwisePeriodicLift (b : Bool) : C(ℝ, TriangleRegularPoint) :=
  realCurveLift (loopPeriodic (clockwiseRegularMeridian b)) normalizedRegularMeridianBasepoint
    (loopPeriodic_zero (clockwiseRegularMeridian b)).symm

@[simp] theorem clockwisePeriodicLift_projection (b : Bool) (t : ℝ) :
    triangleRegularProject (clockwisePeriodicLift b t) =
      loopPeriodic (clockwiseRegularMeridian b) t :=
  realCurveLift_projection _ _ _ t

@[simp] theorem clockwisePeriodicLift_zero (b : Bool) :
    clockwisePeriodicLift b 0 = normalizedRegularMeridianBasepoint :=
  realCurveLift_zero _ _ _

/-- Covering uniqueness identifies the whole first period with the actual clockwise lift. -/
@[simp] theorem clockwisePeriodicLift_unit (b : Bool) (t : unitInterval) :
    clockwisePeriodicLift b (t : ℝ) = clockwiseFinalLift b t := by
  have he : triangleRegularProject ∘
      (fun u : unitInterval => clockwisePeriodicLift b (u : ℝ)) =
      triangleRegularProject ∘ clockwiseFinalLift b := by
    funext u
    simp only [Function.comp_apply, clockwisePeriodicLift_projection,
      loopPeriodic_unit, clockwiseFinalLift_projection]
  exact congr_fun (triangleRegularProject_covering.isCoveringMap.eq_of_comp_eq
    ((clockwisePeriodicLift b).continuous.comp continuous_subtype_val)
    (clockwiseFinalLift b).continuous he 0
    ((clockwisePeriodicLift_zero b).trans (clockwiseFinalLift_zero b).symm)) t

/-- The one-period endpoint is the same actual deck transformation as in the fixed frame. -/
theorem clockwisePeriodicLift_one (b : Bool) :
    clockwisePeriodicLift b 1 = clockwiseLiftEndpoint b • clockwisePeriodicLift b 0 := by
  rw [clockwisePeriodicLift_zero]
  have h := clockwiseFinalLift_one b
  rw [clockwiseFinalLift_zero] at h
  exact (clockwisePeriodicLift_unit b 1).trans h

/-- The full real lift obeys the integer deck convention of the actual family cylinder. -/
theorem clockwisePeriodicLift_translate (b : Bool) (k : ℤ) (t : ℝ) :
    clockwisePeriodicLift b (t + k) =
      ((clockwiseLiftEndpoint b)⁻¹ ^ (-k)) • clockwisePeriodicLift b t := by
  apply realCurveLift_translate (loopPeriodic (clockwiseRegularMeridian b))
    normalizedRegularMeridianBasepoint (loopPeriodic_zero (clockwiseRegularMeridian b)).symm
    (loopPeriodic_add_one (clockwiseRegularMeridian b)) (clockwiseLiftEndpoint b)⁻¹ _ k t
  change clockwisePeriodicLift b 1 =
    ((clockwiseLiftEndpoint b)⁻¹)⁻¹ • normalizedRegularMeridianBasepoint
  rw [inv_inv, ← clockwisePeriodicLift_zero b]
  exact clockwisePeriodicLift_one b

/-- Equivalently, shifting the real parameter adds the corresponding power of the endpoint. -/
theorem clockwisePeriodicLift_add_int (b : Bool) (t : ℝ) (k : ℤ) :
    clockwisePeriodicLift b (t + (k : ℝ)) =
      (clockwiseLiftEndpoint b ^ k) • clockwisePeriodicLift b t := by
  simpa only [inv_zpow, zpow_neg, inv_inv] using clockwisePeriodicLift_translate b k t

theorem clockwisePeriodicLift_int (b : Bool) (k : ℤ) :
    clockwisePeriodicLift b (k : ℝ) =
      (clockwiseLiftEndpoint b ^ k) • normalizedRegularMeridianBasepoint := by
  simpa only [zero_add, clockwisePeriodicLift_zero] using clockwisePeriodicLift_add_int b 0 k

end Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary
