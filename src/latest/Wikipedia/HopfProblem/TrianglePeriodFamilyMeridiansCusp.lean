import Wikipedia.HopfProblem.TrianglePeriodFamilyMeridiansCuspCoordinates
import Wikipedia.HopfProblem.TrianglePeriodFamilyMeridiansCircle
import Wikipedia.HopfProblem.SpecialPeriodsTriangleCuspRegular
import Wikipedia.HopfProblem.SpecialPeriodsTriangleCuspAtlas
import Mathlib.Topology.Path

/-!
# An explicit positive cusp-meridian lift in the actual regular domain

The horizontal segment `z + width * t`, for `0 ≤ t ≤ 1`, stays inside
the chosen high horodisc and hence in the actual regular triangle locus.
Its endpoint is the inverse cusp translate.  Its original exponential
coordinate is exactly `q(z) * exp(2πit)`, giving one positive turn around
zero in the actual compactified cusp chart.

This construction has no period-map parameter and does not assert a
transport convention.  Projecting the specified lift and computing its
transport are separate operations.
-/

noncomputable section

open Function Set Topology UpperHalfPlane

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Meridians

open SpecialPeriods

/-- The chosen high-horodisc point, as a point of the actual regular
upper-half-plane domain. -/
def cuspBasePoint (Y : ℝ) (hY : Triangle.width ≤ Y) (z : Triangle.horodisc Y) :
    TriangleRegularPoint :=
  ⟨z, Triangle.horodisc_subset_triangleRegularLocus Y hY z.property⟩

@[simp] theorem cuspBasePoint_coe (Y : ℝ) (hY : Triangle.width ≤ Y)
    (z : Triangle.horodisc Y) : (cuspBasePoint Y hY z : ℍ) = (z : ℍ) := rfl

/-- The full horizontal line used to construct the cusp lift.  Every
point remains regular because its imaginary part is unchanged. -/
def cuspHorizontalPoint (Y : ℝ) (hY : Triangle.width ≤ Y)
    (z : Triangle.horodisc Y) (s : ℝ) : TriangleRegularPoint :=
  ⟨(Triangle.width * s) +ᵥ (z : ℍ),
    Triangle.horodisc_subset_triangleRegularLocus Y hY (by
      change Y < ((Triangle.width * s) +ᵥ (z : ℍ)).im
      rw [UpperHalfPlane.vadd_im]
      exact z.property)⟩

@[simp] theorem cuspHorizontalPoint_coe (Y : ℝ) (hY : Triangle.width ≤ Y)
    (z : Triangle.horodisc Y) (s : ℝ) :
    (cuspHorizontalPoint Y hY z s : ℍ) = (Triangle.width * s) +ᵥ (z : ℍ) := rfl

theorem cuspHorizontalPoint_continuous (Y : ℝ) (hY : Triangle.width ≤ Y)
    (z : Triangle.horodisc Y) : Continuous (cuspHorizontalPoint Y hY z) := by
  apply IsInducing.subtypeVal.continuous_iff.mpr
  apply UpperHalfPlane.isEmbedding_coe.continuous_iff.mpr
  change Continuous (fun s : ℝ => ((Triangle.width * s : ℝ) : ℂ) + (z : ℍ))
  exact (Complex.continuous_ofReal.comp (continuous_const.mul continuous_id)).add continuous_const

@[simp] theorem cuspHorizontalPoint_zero (Y : ℝ) (hY : Triangle.width ≤ Y)
    (z : Triangle.horodisc Y) : cuspHorizontalPoint Y hY z 0 = cuspBasePoint Y hY z := by
  apply Subtype.ext
  change (Triangle.width * 0) +ᵥ (z : ℍ) = (z : ℍ)
  simp

@[simp] theorem cuspHorizontalPoint_one (Y : ℝ) (hY : Triangle.width ≤ Y)
    (z : Triangle.horodisc Y) :
    cuspHorizontalPoint Y hY z 1 = triangleCuspGenerator⁻¹ • cuspBasePoint Y hY z := by
  apply Subtype.ext
  change (Triangle.width * 1) +ᵥ (z : ℍ) =
    triangleGeometricRepresentation triangleCuspGenerator⁻¹ (z : ℍ)
  simpa using (triangleGeometricRepresentation_cusp_zpow_apply (-1) (z : ℍ)).symm

/-- The explicit counterclockwise cusp lift.  Its inverse-generator
endpoint is part of its actual path type, not an additional hypothesis. -/
def cuspCCWLift (Y : ℝ) (hY : Triangle.width ≤ Y) (z : Triangle.horodisc Y) :
    Path (cuspBasePoint Y hY z) (triangleCuspGenerator⁻¹ • cuspBasePoint Y hY z) where
  toFun t := cuspHorizontalPoint Y hY z (t : ℝ)
  continuous_toFun := (cuspHorizontalPoint_continuous Y hY z).comp continuous_subtype_val
  source' := cuspHorizontalPoint_zero Y hY z
  target' := cuspHorizontalPoint_one Y hY z

/-- The literal horizontal segment underlying the path. -/
@[simp] theorem cuspCCWLift_coe (Y : ℝ) (hY : Triangle.width ≤ Y)
    (z : Triangle.horodisc Y) (t : unitInterval) :
    (cuspCCWLift Y hY z t : ℍ) = (Triangle.width * (t : ℝ)) +ᵥ (z : ℍ) := rfl

@[simp] theorem cuspCCWLift_im (Y : ℝ) (hY : Triangle.width ≤ Y)
    (z : Triangle.horodisc Y) (t : unitInterval) :
    (cuspCCWLift Y hY z t : ℍ).im = (z : ℍ).im := by
  rw [cuspCCWLift_coe, UpperHalfPlane.vadd_im]

theorem cuspCCWLift_mem_horodisc (Y : ℝ) (hY : Triangle.width ≤ Y)
    (z : Triangle.horodisc Y) (t : unitInterval) :
    (cuspCCWLift Y hY z t : ℍ) ∈ Triangle.horodisc Y := by
  change Y < (cuspCCWLift Y hY z t : ℍ).im
  rw [cuspCCWLift_im]
  exact z.property

/-- The original exponential coordinate follows the literal positive
once-around complex circle along the specified lift. -/
theorem cuspCCWLift_q_exp (Y : ℝ) (hY : Triangle.width ≤ Y)
    (z : Triangle.horodisc Y) (t : unitInterval) :
    Triangle.cuspQ (cuspCCWLift Y hY z t : ℍ) =
      Triangle.cuspQ (z : ℍ) * Complex.exp (2 * Real.pi * Complex.I * ((t : ℝ) : ℂ)) := by
  rw [cuspCCWLift_coe]
  exact cuspQ_horizontal_translate (z : ℍ) (t : ℝ)

theorem cuspCCWLift_q (Y : ℝ) (hY : Triangle.width ≤ Y)
    (z : Triangle.horodisc Y) (t : unitInterval) :
    Triangle.cuspQ (cuspCCWLift Y hY z t : ℍ) = Triangle.cuspQ (z : ℍ) * turn (t : ℝ) :=
  cuspCCWLift_q_exp Y hY z t

theorem cuspCCWLift_q_norm (Y : ℝ) (hY : Triangle.width ≤ Y)
    (z : Triangle.horodisc Y) (t : unitInterval) :
    ‖Triangle.cuspQ (cuspCCWLift Y hY z t : ℍ)‖ = ‖Triangle.cuspQ (z : ℍ)‖ := by
  rw [cuspCCWLift_coe]
  exact cuspQ_horizontal_translate_norm (z : ℍ) (t : ℝ)

theorem cuspCCWLift_q_ne_zero (Y : ℝ) (hY : Triangle.width ≤ Y)
    (z : Triangle.horodisc Y) (t : unitInterval) :
    Triangle.cuspQ (cuspCCWLift Y hY z t : ℍ) ≠ 0 :=
  Triangle.cuspQ_ne_zero _

theorem cuspCCWLift_chart_source (Y : ℝ) (hY : Triangle.width ≤ Y)
    (z : Triangle.horodisc Y) (t : unitInterval) :
    triangleCompactifiedProjection (cuspCCWLift Y hY z t : ℍ) ∈
      (Triangle.cuspFullChart Y hY).source := by
  rw [Triangle.cuspFullChart_source]
  apply (Triangle.openInclusion_mem_cuspNeighborhood Y _).mpr
  exact ⟨(cuspCCWLift Y hY z t : ℍ), cuspCCWLift_mem_horodisc Y hY z t, rfl⟩

/-- The actual compactified quotient chart has precisely that same
coordinate on every point of the lifted segment. -/
theorem cuspCCWLift_chart_eq_q (Y : ℝ) (hY : Triangle.width ≤ Y)
    (z : Triangle.horodisc Y) (t : unitInterval) :
    Triangle.cuspFullChart Y hY
      (triangleCompactifiedProjection (cuspCCWLift Y hY z t : ℍ)) =
      Triangle.cuspQ (cuspCCWLift Y hY z t : ℍ) :=
  Triangle.cuspFullChart_mk Y hY
    ⟨(cuspCCWLift Y hY z t : ℍ), cuspCCWLift_mem_horodisc Y hY z t⟩

theorem cuspCCWLift_chart_exp (Y : ℝ) (hY : Triangle.width ≤ Y)
    (z : Triangle.horodisc Y) (t : unitInterval) :
    Triangle.cuspFullChart Y hY
      (triangleCompactifiedProjection (cuspCCWLift Y hY z t : ℍ)) =
      Triangle.cuspQ (z : ℍ) * Complex.exp (2 * Real.pi * Complex.I * ((t : ℝ) : ℂ)) := by
  rw [cuspCCWLift_chart_eq_q, cuspCCWLift_q_exp]

theorem cuspCCWLift_chart (Y : ℝ) (hY : Triangle.width ≤ Y)
    (z : Triangle.horodisc Y) (t : unitInterval) :
    Triangle.cuspFullChart Y hY
      (triangleCompactifiedProjection (cuspCCWLift Y hY z t : ℍ)) =
      Triangle.cuspQ (z : ℍ) * turn (t : ℝ) :=
  cuspCCWLift_chart_exp Y hY z t

theorem cuspCCWLift_chart_norm (Y : ℝ) (hY : Triangle.width ≤ Y)
    (z : Triangle.horodisc Y) (t : unitInterval) :
    ‖Triangle.cuspFullChart Y hY
      (triangleCompactifiedProjection (cuspCCWLift Y hY z t : ℍ))‖ =
      ‖Triangle.cuspQ (z : ℍ)‖ := by
  rw [cuspCCWLift_chart_eq_q, cuspCCWLift_q_norm]

theorem cuspCCWLift_chart_ne_zero (Y : ℝ) (hY : Triangle.width ≤ Y)
    (z : Triangle.horodisc Y) (t : unitInterval) :
    Triangle.cuspFullChart Y hY
      (triangleCompactifiedProjection (cuspCCWLift Y hY z t : ℍ)) ≠ 0 := by
  rw [cuspCCWLift_chart_eq_q]
  exact cuspCCWLift_q_ne_zero Y hY z t

end Wikipedia.HopfProblem.TrianglePeriodFamily.Meridians
