import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryOrientation
import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryEllipticPeriodicLiftClockwise

/-!
# The canonical positive real lift in the actual elliptic frame

Reverse the parameter of the actual clockwise periodic lift.  The proved
normalization orientation and the integer deck relation identify its
whole first period with the already constructed positive compatible lift.
Its projection and every integer translate therefore retain the original
meridian and its actual deck generator, including after any real phase shift.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary

open SpecialPeriods SpecialPeriods.Triangle Meridians BoundaryLoopSquares

private theorem clockwiseEndpoint_eq_generator (b : Bool) :
    clockwiseLiftEndpoint b = compatibleMeridianGenerator b := by
  simp only [clockwiseLiftEndpoint, normalizationReversesMeridians_false,
    Bool.false_eq_true, if_false]

private theorem clockwiseFinalLift_eq_reverse (b : Bool) (t : unitInterval) :
    clockwiseFinalLift b t =
      compatibleMeridianGenerator b • compatibleMeridianLift b (unitInterval.symm t) := by
  rw [clockwiseFinalLift, normalizationReversesMeridians_false]
  rfl

/-- The actual positive real lift is the parameter reversal of the fixed clockwise lift. -/
def canonicalPositiveLift (b : Bool) : C(ℝ, TriangleRegularPoint) :=
  (clockwisePeriodicLift b).comp ⟨fun t : ℝ => -t, continuous_neg⟩

@[simp] theorem canonicalPositiveLift_apply (b : Bool) (t : ℝ) :
    canonicalPositiveLift b t = clockwisePeriodicLift b (-t) := rfl

@[simp] theorem canonicalPositiveLift_zero (b : Bool) :
    canonicalPositiveLift b 0 = normalizedRegularMeridianBasepoint := by
  rw [canonicalPositiveLift_apply, neg_zero, clockwisePeriodicLift_zero]

/-- The complete positive first period is the original compatible meridian lift. -/
@[simp] theorem canonicalPositiveLift_unit (b : Bool) (t : unitInterval) :
    canonicalPositiveLift b (t : ℝ) = compatibleMeridianLift b t := by
  calc
    _ = clockwisePeriodicLift b ((unitInterval.symm t : ℝ) + (-1 : ℝ)) := by
      rw [canonicalPositiveLift_apply, unitInterval.coe_symm_eq]
      congr 1
      ring
    _ = (clockwiseLiftEndpoint b ^ (-1 : ℤ)) •
        clockwisePeriodicLift b (unitInterval.symm t : ℝ) := by
      simpa only [Int.cast_neg, Int.cast_one] using
        clockwisePeriodicLift_add_int b (unitInterval.symm t : ℝ) (-1)
    _ = (compatibleMeridianGenerator b)⁻¹ •
        (compatibleMeridianGenerator b • compatibleMeridianLift b t) := by
      rw [clockwiseEndpoint_eq_generator, zpow_neg_one, clockwisePeriodicLift_unit,
        clockwiseFinalLift_eq_reverse, unitInterval.symm_symm]
    _ = _ := inv_smul_smul _ _

/-- The positive lift ends at the inverse actual compatible generator. -/
theorem canonicalPositiveLift_one (b : Bool) :
    canonicalPositiveLift b 1 =
      (compatibleMeridianGenerator b)⁻¹ • normalizedRegularMeridianBasepoint :=
  (canonicalPositiveLift_unit b 1).trans (compatibleMeridianLift b).target

/-- Every integer shift retains the source's inverse-generator convention. -/
theorem canonicalPositiveLift_translate (b : Bool) (k : ℤ) (t : ℝ) :
    canonicalPositiveLift b (t + k) =
      (compatibleMeridianGenerator b ^ (-k)) • canonicalPositiveLift b t := by
  simpa only [canonicalPositiveLift_apply, neg_add, Int.cast_neg,
    clockwiseEndpoint_eq_generator] using clockwisePeriodicLift_add_int b (-t) (-k)

theorem canonicalPositiveLift_int (b : Bool) (k : ℤ) :
    canonicalPositiveLift b (k : ℝ) =
      (compatibleMeridianGenerator b ^ (-k)) • normalizedRegularMeridianBasepoint := by
  simpa only [zero_add, canonicalPositiveLift_zero] using canonicalPositiveLift_translate b k 0

/-- The projection is the actual positive meridian extended periodically to all real times. -/
theorem canonicalPositiveLift_projection (b : Bool) (t : ℝ) :
    triangleRegularProject (canonicalPositiveLift b t) =
      loopPeriodic (compatibleRegularMeridian b) t := by
  have hp : Function.Periodic
      (fun u : ℝ => triangleRegularProject (canonicalPositiveLift b u)) 1 := by
    intro u
    have h := congrArg triangleRegularProject (canonicalPositiveLift_translate b 1 u)
    simpa only [Int.cast_one, triangleRegularProject_covering.map_smul] using h
  have hu (u : unitInterval) :
      triangleRegularProject (canonicalPositiveLift b (u : ℝ)) = compatibleRegularMeridian b u := by
    rw [canonicalPositiveLift_unit]
    exact compatibleLift_projection b u
  exact congrFun (loopPeriodic_unique
    (p := compatibleRegularMeridian b)
    (fun u : ℝ => triangleRegularProject (canonicalPositiveLift b u)) hp hu) t

/-- Shift the real parameter without changing the actual positive covering lift. -/
def canonicalPositivePhaseLift (b : Bool) (phase : ℝ) : C(ℝ, TriangleRegularPoint) :=
  (canonicalPositiveLift b).comp ⟨fun t => t + phase, continuous_id.add continuous_const⟩

@[simp] theorem canonicalPositivePhaseLift_apply (b : Bool) (phase t : ℝ) :
    canonicalPositivePhaseLift b phase t = canonicalPositiveLift b (t + phase) := rfl

theorem canonicalPositivePhaseLift_projection (b : Bool) (phase t : ℝ) :
    triangleRegularProject (canonicalPositivePhaseLift b phase t) =
      loopPeriodic (compatibleRegularMeridian b) (t + phase) :=
  canonicalPositiveLift_projection b (t + phase)

theorem canonicalPositivePhaseLift_translate (b : Bool) (phase : ℝ) (k : ℤ) (t : ℝ) :
    canonicalPositivePhaseLift b phase (t + k) =
      (compatibleMeridianGenerator b ^ (-k)) • canonicalPositivePhaseLift b phase t := by
  simp only [canonicalPositivePhaseLift_apply]
  rw [show t + (k : ℝ) + phase = (t + phase) + k by ring]
  exact canonicalPositiveLift_translate b k (t + phase)

end Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary
