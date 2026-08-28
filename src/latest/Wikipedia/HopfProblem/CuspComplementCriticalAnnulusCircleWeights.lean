import Wikipedia.HopfProblem.CuspComplementCriticalAnnulusTransitions
import Wikipedia.HopfProblem.CuspCircleNormalTrivializationEquivariance
import Wikipedia.HopfProblem.CuspCircleOrbitLocalParameter

/-!
# The original opposite circle weights on the two remaining double curves

Every finite parameter lies on its literal time-zero toric axis, without
a normal-radius or annulus-membership restriction. The original global
multiplicative action therefore acts with weights one and minus one on
the two original curve parameters. The upper chart retains its actual
correction-dependent factor and acquires the opposite weight.
-/

noncomputable section

open Set Topology
open scoped Matrix OnePoint

namespace Wikipedia.HopfProblem.CuspComplement.CriticalAnnulus

open ToricCharts ToricFan ToricFan.Triangle ToricSpace
open CuspCircleNormalTrivialization SpecialPeriods SpecialPeriods.Threefold
open SpecialPeriods.Threefold.VerticalAction SpecialPeriods.Threefold.Homology

local notation "CD" => CuspGeometry.data
local notation "Circle" => AddCircle (1 : ℝ)

/-- The original affine parameter has weight one on curve zero and minus one on curve two. -/
def curveMultiplier : Bool → ℂˣ → ℂ
  | false, u => u
  | true, u => ↑(u⁻¹)

@[simp] theorem curveMultiplier_false (u : ℂˣ) : curveMultiplier false u = (u : ℂ) := rfl

@[simp] theorem curveMultiplier_true (u : ℂˣ) : curveMultiplier true u = (u : ℂ)⁻¹ := by
  simp [curveMultiplier]

theorem curveMultiplier_ne_zero (b : Bool) (u : ℂˣ) : curveMultiplier b u ≠ 0 := by
  cases b <;> exact Units.ne_zero _

@[simp] theorem curveMultiplier_one (b : Bool) : curveMultiplier b 1 = 1 := by
  cases b <;> simp [curveMultiplier]

theorem curveMultiplier_mul (b : Bool) (u v : ℂˣ) :
    curveMultiplier b (u * v) = curveMultiplier b u * curveMultiplier b v := by
  cases b <;> simp [curveMultiplier, mul_inv_rev, mul_comm]

theorem curveMultiplier_inv (b : Bool) (u : ℂˣ) :
    curveMultiplier b u⁻¹ = (curveMultiplier b u)⁻¹ := by
  cases b <;> simp [curveMultiplier]

theorem curveMultiplier_norm (b : Bool) (u : ℂˣ) (hu : ‖(u : ℂ)‖ = 1) :
    ‖curveMultiplier b u‖ = 1 := by
  cases b <;> simp [curveMultiplier, norm_inv, hu]

theorem curveMultiplier_norm_mul (b : Bool) (u : ℂˣ) (hu : ‖(u : ℂ)‖ = 1) (z : ℂ) :
    ‖curveMultiplier b u * z‖ = ‖z‖ := by
  rw [norm_mul, curveMultiplier_norm b u hu, one_mul]

theorem curveMultiplier_continuous (b : Bool) : Continuous (curveMultiplier b) := by
  cases b
  · exact Units.continuous_val
  · exact Units.continuous_val.comp continuous_inv

/-- Every original coordinate axis lies in the actual open cusp domain at time zero. -/
def axisCoordinatePoint (s : Triangle) (i : Fin 3) (z : ℂ) : FixedCoordinates.Domain :=
  ⟨axisPoint s i z, by
    change ‖Triangle.time (axisPoint s i z)‖ < (CD).radius
    rw [Triangle.time_axisPoint, norm_zero]
    exact (CD).radius_pos⟩

@[simp] theorem axisCoordinatePoint_coe (s : Triangle) (i : Fin 3) (z : ℂ) :
    (axisCoordinatePoint s i z : CoordinateSpace 3) = axisPoint s i z := rfl

/-- This native coordinate point maps to the unchanged cusp quotient axis map. -/
theorem globalMap_axisCoordinatePoint (s : Triangle) (i : Fin 3) (z : ℂ) :
    FixedCoordinates.globalMap s (axisCoordinatePoint s i z) =
      CuspGeometry.inclusion
        (CuspQuotient.axisMap (CD).correction (CD).radius (CD).radius_pos s i z) := rfl

/-- Reversed lower-axis indexing gives the two original affine weights. -/
theorem diagonal_lower_axis (b : Bool) (u : ℂˣ) (z : ℂ) :
    FixedCoordinates.diagonal u (axisPoint referenceTriangle (curveIndex b) z) =
      axisPoint referenceTriangle (curveIndex b) (curveMultiplier b u * z) := by
  cases b <;> ext j <;> fin_cases j <;>
    simp [FixedCoordinates.diagonal_apply, curveMultiplier, curveIndex,
      axisPoint, axisIndex, referenceTriangle]

/-- The unchanged upper axes have the opposite weights. -/
theorem diagonal_upper_axis (b : Bool) (u : ℂˣ) (z : ℂ) :
    FixedCoordinates.diagonal u (axisPoint (upperNeighbour 1) (curveIndex b) z) =
      axisPoint (upperNeighbour 1) (curveIndex b) ((curveMultiplier b u)⁻¹ * z) := by
  cases b <;> ext j <;> fin_cases j <;>
    simp [FixedCoordinates.diagonal_apply, curveMultiplier, curveIndex,
      axisPoint, axisIndex, upperNeighbour]

theorem coordinateAction_lower_axis (b : Bool) (u : ℂˣ) (z : ℂ) :
    FixedCoordinates.coordinateAction u
        (axisCoordinatePoint referenceTriangle (curveIndex b) z) =
      axisCoordinatePoint referenceTriangle (curveIndex b) (curveMultiplier b u * z) :=
  Subtype.ext (diagonal_lower_axis b u z)

theorem coordinateAction_upper_axis (b : Bool) (u : ℂˣ) (z : ℂ) :
    FixedCoordinates.coordinateAction u
        (axisCoordinatePoint (upperNeighbour 1) (curveIndex b) z) =
      axisCoordinatePoint (upperNeighbour 1) (curveIndex b) ((curveMultiplier b u)⁻¹ * z) :=
  Subtype.ext (diagonal_upper_axis b u z)

/-- Exact equivariance on every original finite curve point, with no radius restriction. -/
theorem actionBiholomorph_doubleCurve_finite (b : Bool) (u : ℂˣ) (z : ℂ) :
    actionBiholomorph u
        (CuspGeometry.doubleCurveParametrization (curveIndex b) (z : RiemannSphere)) =
      CuspGeometry.doubleCurveParametrization (curveIndex b)
        ((curveMultiplier b u * z : ℂ) : RiemannSphere) := by
  change actionBiholomorph u (FixedCoordinates.globalMap referenceTriangle
      (axisCoordinatePoint referenceTriangle (curveIndex b) z)) =
    FixedCoordinates.globalMap referenceTriangle
      (axisCoordinatePoint referenceTriangle (curveIndex b) (curveMultiplier b u * z))
  rw [FixedCoordinates.globalMap_coordinateAction, coordinateAction_lower_axis]

/-- Exact equivariance on the original upper axis, before any annulus restriction. -/
theorem actionBiholomorph_upper_axis (b : Bool) (u : ℂˣ) (z : ℂ) :
    actionBiholomorph u
        (CuspGeometry.inclusion
          (CuspQuotient.axisMap (CD).correction (CD).radius (CD).radius_pos
            (upperNeighbour 1) (curveIndex b) z)) =
      CuspGeometry.inclusion
        (CuspQuotient.axisMap (CD).correction (CD).radius (CD).radius_pos
          (upperNeighbour 1) (curveIndex b) ((curveMultiplier b u)⁻¹ * z)) := by
  change actionBiholomorph u (FixedCoordinates.globalMap (upperNeighbour 1)
      (axisCoordinatePoint (upperNeighbour 1) (curveIndex b) z)) =
    FixedCoordinates.globalMap (upperNeighbour 1)
      (axisCoordinatePoint (upperNeighbour 1) (curveIndex b) ((curveMultiplier b u)⁻¹ * z))
  rw [FixedCoordinates.globalMap_coordinateAction, coordinateAction_upper_axis]

/-- In the actual real normal frame, the original circle acts by scalar multiplication. -/
theorem lowerNormal_curveMultiplier (b : Bool) (u : ℂˣ) (hu : ‖(u : ℂ)‖ = 1) (z : ℂ) :
    lowerNormal b (curveMultiplier b u * z) = (u : ℂ) • lowerNormal b z := by
  have h := congrArg Prod.snd (chartCoordinates_diagonal false u hu
    (axisPoint referenceTriangle (curveIndex b) z))
  simpa only [diagonal_lower_axis, chartCoordinates_lower_axis] using h

theorem upperNormal_curveMultiplier (b : Bool) (u : ℂˣ) (hu : ‖(u : ℂ)‖ = 1) (z : ℂ) :
    upperNormal b ((curveMultiplier b u)⁻¹ * z) = (u : ℂ) • upperNormal b z := by
  have h := congrArg Prod.snd (chartCoordinates_diagonal true u hu
    (axisPoint (upperNeighbour 1) (curveIndex b) z))
  simpa only [diagonal_upper_axis, chartCoordinates_upper_axis] using h

/-- The original upper factor is retained literally, including its complex phase. -/
theorem kappa_mul_inv_curveMultiplier (b : Bool) (u : ℂˣ) (z : ℂ) :
    kappa b * (curveMultiplier b u * z)⁻¹ =
      (curveMultiplier b u)⁻¹ * (kappa b * z⁻¹) := by
  rw [mul_inv_rev]
  ac_rfl

theorem kappa_mul_inv_curveMultiplier_norm (b : Bool) (u : ℂˣ)
    (hu : ‖(u : ℂ)‖ = 1) (z : ℂ) :
    ‖kappa b * (curveMultiplier b u * z)⁻¹‖ = ‖kappa b * z⁻¹‖ := by
  rw [kappa_mul_inv_curveMultiplier, norm_mul, norm_inv,
    curveMultiplier_norm b u hu, inv_one, one_mul]

/-- The finite original curve point transforms in the upper chart by the opposite phase. -/
theorem actionBiholomorph_doubleCurve_upper (b : Bool) (u : ℂˣ) (z : ℂ) (hz : z ≠ 0) :
    actionBiholomorph u
        (CuspGeometry.doubleCurveParametrization (curveIndex b) (z : RiemannSphere)) =
      CuspGeometry.inclusion
        (CuspQuotient.axisMap (CD).correction (CD).radius (CD).radius_pos
          (upperNeighbour 1) (curveIndex b)
          ((curveMultiplier b u)⁻¹ * (kappa b * z⁻¹))) :=
  (congrArg (actionBiholomorph u) (doubleCurve_upper b z hz)).trans
    (actionBiholomorph_upper_axis b u (kappa b * z⁻¹))

theorem curveMultiplier_circle_norm (b : Bool) (t : Circle) :
    ‖curveMultiplier b (DeltaSweep.circleParameter t)‖ = 1 :=
  curveMultiplier_norm b _ (FixedCoordinates.CircleOrbit.circleParameter_norm t)

theorem curveMultiplier_circle_continuous (b : Bool) :
    Continuous (fun t : Circle => curveMultiplier b (DeltaSweep.circleParameter t)) :=
  (curveMultiplier_continuous b).comp DeltaSweep.circleParameter_continuous

/-- The actual period-one delta action has these same weights on the original finite points. -/
theorem deltaAction_doubleCurve_finite (b : Bool) (t : Circle) (z : ℂ) :
    DeltaSweep.actionMap
        (t, CuspGeometry.doubleCurveParametrization (curveIndex b) (z : RiemannSphere)) =
      CuspGeometry.doubleCurveParametrization (curveIndex b)
        ((curveMultiplier b (DeltaSweep.circleParameter t) * z : ℂ) : RiemannSphere) :=
  actionBiholomorph_doubleCurve_finite b (DeltaSweep.circleParameter t) z

end Wikipedia.HopfProblem.CuspComplement.CriticalAnnulus
