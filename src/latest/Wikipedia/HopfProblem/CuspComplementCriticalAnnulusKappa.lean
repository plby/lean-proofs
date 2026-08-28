import Wikipedia.HopfProblem.CuspCircleNormalTrivializationCuspBasic

/-!
# The exact upper-axis multipliers for the two remaining double curves

The original sphere parameters on double curves zero and two use their
own adjacent upper toric charts. The native deck shifts below move those
charts to the frozen upper normal chart. Their correction-dependent
axis multipliers are retained literally, including their complex phases.
-/

noncomputable section

open Set
open scoped Matrix OnePoint

namespace Wikipedia.HopfProblem.CuspComplement.CriticalAnnulus

open ToricCharts ToricFan ToricFan.Triangle ToricSpace
open SpecialPeriods SpecialPeriods.Threefold

local notation "CD" => CuspGeometry.data

/-- The original deck multiplier taking curve zero's upper axis to the fixed normal chart. -/
def kappaZero : ℂ :=
  factors (upperNeighbour 1)
    (fibreMultiplier (exponentialMultiplier (CD).correction ![-1, -1] 0)) 0

/-- The original deck multiplier taking curve two's upper axis to the fixed normal chart. -/
def kappaTwo : ℂ :=
  factors (upperNeighbour 1)
    (fibreMultiplier (exponentialMultiplier (CD).correction ![0, -1] 0)) 2

theorem kappaZero_ne_zero : kappaZero ≠ 0 := factors_nonzero _ _ _

theorem kappaTwo_ne_zero : kappaTwo ≠ 0 := factors_nonzero _ _ _

/-- The literal lattice shift for curve zero's adjacent upper chart. -/
theorem upper_shift_zero :
    (upperNeighbour 0).shift (cuspVector ![-1, -1]) = upperNeighbour 1 := by decide

/-- The literal lattice shift for curve two's adjacent upper chart. -/
theorem upper_shift_two :
    (upperNeighbour 2).shift (cuspVector ![0, -1]) = upperNeighbour 1 := by decide

/-- Every original affine sphere parameter is the unchanged lower reference-axis map. -/
theorem doubleCurve_lower (i : Fin 3) (z : ℂ) :
    CuspGeometry.doubleCurveParametrization i (z : RiemannSphere) =
      CuspGeometry.inclusion
        (CuspQuotient.axisMap (CD).correction (CD).radius (CD).radius_pos
          referenceTriangle i z) := rfl

/-- Curve zero in the fixed upper normal chart, with its exact correction multiplier. -/
theorem doubleCurve_zero_upper (z : ℂ) (hz : z ≠ 0) :
    CuspGeometry.doubleCurveParametrization 0 (z : RiemannSphere) =
      CuspGeometry.inclusion
        (CuspQuotient.axisMap (CD).correction (CD).radius (CD).radius_pos
          (upperNeighbour 1) 0 (kappaZero * z⁻¹)) := by
  change CuspGeometry.inclusion
      (CuspQuotient.axisMap (CD).correction (CD).radius (CD).radius_pos
        referenceTriangle 0 z) = _
  apply congrArg CuspGeometry.inclusion
  rw [CuspQuotient.axisMap_inversion (CD).correction (CD).radius (CD).radius_pos 0 hz]
  have h := CuspQuotient.axisMap_shift (CD).correction (CD).radius (CD).radius_pos
    ![-1, -1] (upperNeighbour 0) 0 z⁻¹
  rw [upper_shift_zero] at h
  exact h.symm

/-- Curve two in the fixed upper normal chart, with its exact correction multiplier. -/
theorem doubleCurve_two_upper (z : ℂ) (hz : z ≠ 0) :
    CuspGeometry.doubleCurveParametrization 2 (z : RiemannSphere) =
      CuspGeometry.inclusion
        (CuspQuotient.axisMap (CD).correction (CD).radius (CD).radius_pos
          (upperNeighbour 1) 2 (kappaTwo * z⁻¹)) := by
  change CuspGeometry.inclusion
      (CuspQuotient.axisMap (CD).correction (CD).radius (CD).radius_pos
        referenceTriangle 2 z) = _
  apply congrArg CuspGeometry.inclusion
  rw [CuspQuotient.axisMap_inversion (CD).correction (CD).radius (CD).radius_pos 2 hz]
  have h := CuspQuotient.axisMap_shift (CD).correction (CD).radius (CD).radius_pos
    ![0, -1] (upperNeighbour 2) 2 z⁻¹
  rw [upper_shift_two] at h
  exact h.symm

end Wikipedia.HopfProblem.CuspComplement.CriticalAnnulus
