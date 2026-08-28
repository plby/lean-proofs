import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryCuspInversion
import Wikipedia.HopfProblem.TrianglePeriodFamilyFundamentalGroupOuterMeridianPaths

/-!
# The native cusp loop deforms to the fixed clockwise outer circle

After the reciprocal analytic deformation, a literal center-and-phase
interpolation moves the clockwise radius-two circle about zero to the
fixed radius-two circle about one half, starting at its bottom point.
Every intermediate circle stays at distance two from a center in the
real interval from zero to one half, so neither puncture is crossed.
The complete continuous square retains the original basepoint path.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.Cusp

open SpecialPeriods SpecialPeriods.Triangle SpecialPeriods.EllipticAttachingMeridians

/-- Rotate the starting radius continuously from the positive real axis to the bottom. -/
def outerDeformationCoefficient (s : unitInterval) : ℂ :=
  2 * Complex.exp ((-(Real.pi : ℂ) / 2 * Complex.I) * ((s : ℝ) : ℂ))

@[simp] theorem outerDeformationCoefficient_zero : outerDeformationCoefficient 0 = 2 := by
  simp [outerDeformationCoefficient]

@[simp] theorem outerDeformationCoefficient_one :
    outerDeformationCoefficient 1 = -2 * Complex.I := by
  simp [outerDeformationCoefficient, Complex.exp_neg_pi_div_two_mul_I]

/-- The interpolated starting radius has its exact constant norm. -/
theorem outerDeformationCoefficient_norm (s : unitInterval) :
    ‖outerDeformationCoefficient s‖ = 2 := by
  simp [outerDeformationCoefficient, Complex.norm_exp]

/-- The literal center-and-phase deformation of the whole circle. -/
def outerDeformation (s t : unitInterval) : ℂ :=
  (((s : ℝ) / 2 : ℝ) : ℂ) + outerDeformationCoefficient s * clockwiseUnit t

theorem outerDeformation_continuous :
    Continuous (fun p : unitInterval × unitInterval => outerDeformation p.1 p.2) := by
  unfold outerDeformation outerDeformationCoefficient clockwiseUnit
  fun_prop

/-- The entire deformation keeps exactly radius two about its moving center. -/
theorem outerDeformation_norm (s t : unitInterval) :
    ‖outerDeformation s t - (((s : ℝ) / 2 : ℝ) : ℂ)‖ = 2 := by
  simp only [outerDeformation, add_sub_cancel_left, norm_mul,
    outerDeformationCoefficient_norm, norm_clockwiseUnit, mul_one]

/-- No point of the actual deformation meets either deleted point. -/
theorem outerDeformation_mem (s t : unitInterval) :
    outerDeformation s t ∈ twicePuncturedPlaneDomain := by
  change outerDeformation s t ≠ 0 ∧ outerDeformation s t ≠ 1
  have hs0 : 0 ≤ (s : ℝ) / 2 := div_nonneg s.property.1 (by norm_num)
  have hs1 : 0 ≤ 1 - (s : ℝ) / 2 := by linarith [s.property.2]
  constructor
  · intro he
    have hn := outerDeformation_norm s t
    rw [he, zero_sub, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hs0] at hn
    linarith [s.property.2]
  · intro he
    have hn := outerDeformation_norm s t
    rw [he, show (1 : ℂ) - (((s : ℝ) / 2 : ℝ) : ℂ) =
      ((1 - (s : ℝ) / 2 : ℝ) : ℂ) by push_cast; rfl,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs1] at hn
    linarith [s.property.1]

/-- The fixed reversed outer path has precisely the endpoint coefficient
of the literal deformation, on every point of the actual interval. -/
theorem outerCircle_symm_coefficient (t : unitInterval) :
    ((outerPositiveCircle 2 (le_refl 2)).symm t : ℂ) =
      (1 / 2 : ℂ) + (-2 * Complex.I) * clockwiseUnit t := by
  change (outerPositiveCircle 2 (le_refl 2) (unitInterval.symm t) : ℂ) = _
  rw [outerPositiveCircle_coe, unitInterval.coe_symm_eq]
  unfold circleMap clockwiseUnit
  push_cast
  rw [show (-(Real.pi : ℂ) / 2 + 2 * Real.pi * (1 - ((t : ℝ) : ℂ))) * Complex.I =
    (-(Real.pi : ℂ) / 2 * Complex.I +
      (-(2 * Real.pi : ℂ) * Complex.I * ((t : ℝ) : ℂ))) +
        2 * Real.pi * Complex.I by ring,
    Complex.exp_periodic, Complex.exp_add, Complex.exp_neg_pi_div_two_mul_I]
  ring

/-- A genuine continuous square from the inverse analytic-circle target
to the fixed clockwise outer circle. -/
def inverseOuterSquare :
    LoopSquare inverseMeridian ((outerPositiveCircle 2 (le_refl 2)).symm) := by
  refine LoopSquare.ofContinuous
    (fun p => ⟨outerDeformation p.1 p.2, outerDeformation_mem p.1 p.2⟩)
    (outerDeformation_continuous.subtype_mk _) ?_ ?_ ?_
  · intro t
    apply Subtype.ext
    change outerDeformation 0 t = (inverseMeridian t : ℂ)
    rw [inverseMeridian_coe]
    simp [outerDeformation]
  · intro t
    apply Subtype.ext
    rw [outerCircle_symm_coefficient]
    simp [outerDeformation]
  · intro s
    apply Subtype.ext
    simp only [outerDeformation, clockwiseUnit_zero, clockwiseUnit_one]

/-- The full original native cusp loop is now compared with the exact
fixed outer path by an actual square in the regular quotient. -/
def nativeOuterSquare :
    LoopSquare (nativeLoop controlledHeight)
      (((outerPositiveCircle 2 (le_refl 2)).symm).map
        triangleRegularPlaneHomeomorph.symm.continuous) :=
  nativeReciprocalSquare.trans
    (inverseOuterSquare.postcompose triangleRegularPlaneHomeomorph.symm
      triangleRegularPlaneHomeomorph.symm.continuous)

end Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.Cusp
