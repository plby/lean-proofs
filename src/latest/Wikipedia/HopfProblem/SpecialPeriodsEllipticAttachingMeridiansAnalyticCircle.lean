import Wikipedia.HopfProblem.SpecialPeriodsEllipticAttachingMeridiansLinearization
import Wikipedia.HopfProblem.SpecialPeriodsEllipticAttachingMeridiansCircleBasic
import Wikipedia.HopfProblem.SpecialPeriodsEllipticAttachingMeridiansHomotopy

/-!
# Actual analytic chart circles deform to round meridians

The quantitative noncritical-coordinate estimates produce a literal
continuous family of loops in the twice-punctured plane. It begins with
the image of a small clockwise chart circle under the actual analytic
map and ends with its nonzero linear part. The basepoint trajectory is
the actual straight interpolation at the circle's starting point.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.SpecialPeriods.EllipticAttachingMeridians

open Triangle

namespace LinearizationControl

variable {f : ℂ → ℂ} (D : LinearizationControl f)

/-- The whole small interpolation avoids both actual deleted points. -/
theorem interpolate_mem (b : Bool) (hc : f 0 = center b) (s : unitInterval)
    {z : ℂ} (hz : ‖z‖ < D.radius) (hz0 : z ≠ 0) :
    interpolate f s z ∈ twicePuncturedPlaneDomain := by
  have hn : ‖interpolate f s z - f 0‖ < 1 :=
    (D.interpolate_norm_le s hz).trans_lt (by norm_num)
  have hm := center_add_mem_twicePuncturedPlaneDomain b
    (sub_ne_zero.mpr (D.interpolate_ne_center s hz hz0)) hn
  have he : center b + (interpolate f s z - f 0) = interpolate f s z := by
    rw [← hc]
    ring
  rwa [he] at hm

variable (b : Bool) (hc : f 0 = center b) (A : ℂ) (hA : A ≠ 0)
  (hAr : ‖A‖ < D.radius)

include hAr in
theorem parameterCircle_norm_lt (t : unitInterval) : ‖A * clockwiseUnit t‖ < D.radius := by
  simpa only [norm_mul, norm_clockwiseUnit, mul_one] using hAr

include hA in
theorem parameterCircle_ne_zero (t : unitInterval) : A * clockwiseUnit t ≠ 0 :=
  mul_ne_zero hA (clockwiseUnit_ne_zero t)

/-- The actual starting value of the small analytic coordinate loop. -/
def analyticCircleBasepoint : TwicePuncturedPlane :=
  ⟨f A, by simpa only [interpolate_zero] using D.interpolate_mem b hc 0 hAr hA⟩

@[simp] theorem analyticCircleBasepoint_coe :
    (D.analyticCircleBasepoint b hc A hA hAr : ℂ) = f A := rfl

include D b hc hA hAr in
theorem analyticCircle_mem (t : unitInterval) :
    f (A * clockwiseUnit t) ∈ twicePuncturedPlaneDomain := by
  simpa only [interpolate_zero] using
    D.interpolate_mem b hc 0 (D.parameterCircle_norm_lt A hAr t)
      (parameterCircle_ne_zero A hA t)

include D hAr in
theorem analyticCircle_continuous : Continuous (fun t : unitInterval => f (A * clockwiseUnit t)) :=
  D.continuousOn.comp_continuous (continuous_const.mul clockwiseUnit_continuous) (fun t => by
    rw [Metric.mem_ball, dist_zero_right]
    exact D.parameterCircle_norm_lt A hAr t)

/-- The actual clockwise chart circle mapped into the literal punctured
plane by the supplied analytic function. -/
def analyticCirclePath :
    Path (D.analyticCircleBasepoint b hc A hA hAr)
      (D.analyticCircleBasepoint b hc A hA hAr) where
  toFun t := ⟨f (A * clockwiseUnit t), D.analyticCircle_mem b hc A hA hAr t⟩
  continuous_toFun := (D.analyticCircle_continuous A hAr).subtype_mk _
  source' := Subtype.ext (by simp)
  target' := Subtype.ext (by simp)

@[simp] theorem analyticCirclePath_coe (t : unitInterval) :
    (D.analyticCirclePath b hc A hA hAr t : ℂ) = f (A * clockwiseUnit t) := rfl

include D hA in
theorem linearCoefficient_ne_zero : deriv f 0 * A ≠ 0 :=
  mul_ne_zero D.derivative_ne_zero hA

include D hAr in
theorem linearCoefficient_norm_lt_one : ‖deriv f 0 * A‖ < 1 :=
  (D.linear_small A hAr).trans (by norm_num)

/-- The explicit straight-line family of small analytic and linear
circle images, in the actual two-puncture complement throughout. -/
def analyticCircleSquare :
    LoopSquare (D.analyticCirclePath b hc A hA hAr)
      (clockwiseCirclePath b (deriv f 0 * A) (D.linearCoefficient_ne_zero A hA)
        (D.linearCoefficient_norm_lt_one A hAr)) := by
  let L : unitInterval × unitInterval → ℂ :=
    fun tu => interpolate f tu.1 (A * clockwiseUnit tu.2)
  have hfc : Continuous (fun tu : unitInterval × unitInterval => f (A * clockwiseUnit tu.2)) :=
    (D.analyticCircle_continuous A hAr).comp continuous_snd
  have hL : Continuous L := by
    have ht : Continuous (fun tu : unitInterval × unitInterval => (tu.1 : ℝ)) :=
      continuous_subtype_val.comp continuous_fst
    have hu : Continuous (fun tu : unitInterval × unitInterval => A * clockwiseUnit tu.2) :=
      continuous_const.mul (clockwiseUnit_continuous.comp continuous_snd)
    exact ((Complex.continuous_ofReal.comp (continuous_const.sub ht)).mul hfc).add
      ((Complex.continuous_ofReal.comp ht).mul (continuous_const.add (continuous_const.mul hu)))
  refine LoopSquare.ofContinuous
    (fun tu => ⟨L tu, D.interpolate_mem b hc tu.1
      (D.parameterCircle_norm_lt A hAr tu.2) (parameterCircle_ne_zero A hA tu.2)⟩)
    (hL.subtype_mk _) ?_ ?_ ?_
  · intro u
    apply Subtype.ext
    exact interpolate_zero f _
  · intro u
    apply Subtype.ext
    change interpolate f 1 (A * clockwiseUnit u) =
      center b + (deriv f 0 * A) * clockwiseUnit u
    rw [interpolate_one, hc, mul_assoc]
  · intro t
    apply Subtype.ext
    change interpolate f t (A * clockwiseUnit 0) = interpolate f t (A * clockwiseUnit 1)
    rw [clockwiseUnit_zero, clockwiseUnit_one]

/-- The conjugating path is the actual basepoint trajectory, not an
arbitrary path asserted to preserve a meridian class. -/
@[simp] theorem analyticCircleSquare_tail_coe (t : unitInterval) :
    ((D.analyticCircleSquare b hc A hA hAr).tail t : ℂ) = interpolate f t A := by
  change interpolate f t (A * clockwiseUnit 0) = interpolate f t A
  rw [clockwiseUnit_zero, mul_one]

end LinearizationControl

end Wikipedia.HopfProblem.SpecialPeriods.EllipticAttachingMeridians
