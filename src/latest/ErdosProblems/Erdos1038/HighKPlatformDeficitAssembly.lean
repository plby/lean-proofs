import ErdosProblems.Erdos1038.HighKScalarCalibration

/-!
# Unconditional strict assembly for platform deficit blocks

The centered Fourier calculation supplies the normalized mixed-energy
estimate for every nonempty quantile block.  Consequently the strict finite
platform reduction needs only the scalar margin and the global calibration;
there is no remaining per-block analytic hypothesis.
-/

set_option warningAsError false

open scoped BigOperators

namespace Erdos1038

noncomputable section

/-- Strict finite assembly with the concrete platform deficit energy.  The
centered rearrangement/Fourier estimate is discharged internally. -/
theorem finite_platformDeficitBlock_strict_reduction
    {iota : Type*} [Fintype iota] [Nonempty iota]
    (left right targetRadius : iota → ℝ)
    {k a xMinus xPlus sigmaMinus sigmaPlus Ceff M0 L R0 : ℝ}
    (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    (hxMinus : xMinus < a) (hxPlus : xPlus < a)
    (hsigmaMinus : 0 < sigmaMinus) (hsigmaPlus : 0 < sigmaPlus)
    (hleft : ∀ i, 0 ≤ left i) (hlr : ∀ i, left i < right i)
    (hright : ∀ i, right i ≤ Real.pi)
    (hTargetRadius : ∀ i, 0 < targetRadius i)
    (hAdjointMassSum :
      ∑ i, platformAdjointIntervalMass
        a xMinus xPlus sigmaMinus sigmaPlus (left i) (right i) = R0)
    (hmargin : ∀ i, 0 < circleBlockMargin
      (platformCapacity a) (platformAPi k a)
      (platformBPi a xMinus xPlus sigmaMinus sigmaPlus) Ceff
      (platformReferenceCircleRadius k a (left i) (right i))
      (platformAdjointCircleRadius a xMinus xPlus
        sigmaMinus sigmaPlus (left i) (right i)))
    (hcalibration :
      M0 + (Ceff - platformPotentialConstant k a) * R0 = L) :
    L < M0 + ∑ i, blockRadiusExpression
      (platformReferenceIntervalMass k a (left i) (right i))
      (platformAdjointIntervalMass a xMinus xPlus
        sigmaMinus sigmaPlus (left i) (right i))
      (platformPotentialConstant k a)
      (platformDeficitBlockEnergy k a xMinus xPlus
        sigmaMinus sigmaPlus (left i) (right i))
      (targetRadius i) := by
  apply finite_platformCircleBlock_strict_reduction
    left right
    (fun i ↦ platformDeficitBlockEnergy k a xMinus xPlus
      sigmaMinus sigmaPlus (left i) (right i))
    targetRadius hk ha ha2 hthreshold hxMinus hxPlus
      hsigmaMinus hsigmaPlus hleft hlr hright hTargetRadius
      hAdjointMassSum
  · intro i
    exact circleSelfEnergy_add_gap_le_platformDeficitBlockEnergy_div
      hk ha ha2 hthreshold hxMinus hxPlus hsigmaMinus hsigmaPlus
        (hleft i) (hlr i) (hright i)
  · exact hmargin
  · exact hcalibration

/-- One constant-edge slab certificate now supplies every nonempty block of
the concrete deficit-energy assembly. -/
theorem finite_platformDeficitBlock_strict_reduction_of_constantEdgeCalibration
    {iota : Type*} [Fintype iota] [Nonempty iota]
    (left right targetRadius : iota → ℝ)
    {k a xMinus xPlus sigmaMinus sigmaPlus Ceff M0 L R0 : ℝ}
    (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    (hxMinus : xMinus < a) (hxPlus : xPlus < a)
    (hsigmaMinus : 0 < sigmaMinus) (hsigmaPlus : 0 < sigmaPlus)
    (hleft : ∀ i, 0 ≤ left i) (hlr : ∀ i, left i < right i)
    (hright : ∀ i, right i ≤ Real.pi)
    (hTargetRadius : ∀ i, 0 < targetRadius i)
    (hAdjointMassSum :
      ∑ i, platformAdjointIntervalMass
        a xMinus xPlus sigmaMinus sigmaPlus (left i) (right i) = R0)
    (hcert : PlatformConstantEdgeCalibration
      k a xMinus xPlus sigmaMinus sigmaPlus Ceff)
    (hcalibration :
      M0 + (Ceff - platformPotentialConstant k a) * R0 = L) :
    L < M0 + ∑ i, blockRadiusExpression
      (platformReferenceIntervalMass k a (left i) (right i))
      (platformAdjointIntervalMass a xMinus xPlus
        sigmaMinus sigmaPlus (left i) (right i))
      (platformPotentialConstant k a)
      (platformDeficitBlockEnergy k a xMinus xPlus
        sigmaMinus sigmaPlus (left i) (right i))
      (targetRadius i) := by
  apply finite_platformDeficitBlock_strict_reduction
    left right targetRadius hk ha ha2 hthreshold hxMinus hxPlus
      hsigmaMinus hsigmaPlus hleft hlr hright hTargetRadius
      hAdjointMassSum
  · intro i
    exact platformCircleBlockMargin_pos_of_constantEdgeCalibration
      hk ha ha2 hthreshold hxMinus hxPlus hsigmaMinus hsigmaPlus
        (hleft i) (hlr i) (hright i) hcert
  · exact hcalibration

/-- One affine-edge slab certificate likewise supplies every nonempty block
of the concrete deficit-energy assembly. -/
theorem finite_platformDeficitBlock_strict_reduction_of_affineCalibration
    {iota : Type*} [Fintype iota] [Nonempty iota]
    (left right targetRadius : iota → ℝ)
    {k a xMinus xPlus sigmaMinus sigmaPlus Ceff M0 L R0 : ℝ}
    (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    (hxMinus : xMinus < a) (hxPlus : xPlus < a)
    (hsigmaMinus : 0 < sigmaMinus) (hsigmaPlus : 0 < sigmaPlus)
    (hleft : ∀ i, 0 ≤ left i) (hlr : ∀ i, left i < right i)
    (hright : ∀ i, right i ≤ Real.pi)
    (hTargetRadius : ∀ i, 0 < targetRadius i)
    (hAdjointMassSum :
      ∑ i, platformAdjointIntervalMass
        a xMinus xPlus sigmaMinus sigmaPlus (left i) (right i) = R0)
    (hcert : PlatformAffineCalibration
      k a xMinus xPlus sigmaMinus sigmaPlus Ceff)
    (hcalibration :
      M0 + (Ceff - platformPotentialConstant k a) * R0 = L) :
    L < M0 + ∑ i, blockRadiusExpression
      (platformReferenceIntervalMass k a (left i) (right i))
      (platformAdjointIntervalMass a xMinus xPlus
        sigmaMinus sigmaPlus (left i) (right i))
      (platformPotentialConstant k a)
      (platformDeficitBlockEnergy k a xMinus xPlus
        sigmaMinus sigmaPlus (left i) (right i))
      (targetRadius i) := by
  apply finite_platformDeficitBlock_strict_reduction
    left right targetRadius hk ha ha2 hthreshold hxMinus hxPlus
      hsigmaMinus hsigmaPlus hleft hlr hright hTargetRadius
      hAdjointMassSum
  · intro i
    exact platformCircleBlockMargin_pos_of_affineCalibration
      hk ha ha2 hthreshold hxMinus hxPlus hsigmaMinus hsigmaPlus
        (hleft i) (hlr i) (hright i) hcert
  · exact hcalibration

/-- A terminal scalar certificate also supplies every nonempty block of the
concrete deficit-energy assembly.  This is the assembly interface shared by
the refined terminal slabs and the simple tail certificate. -/
theorem finite_platformDeficitBlock_strict_reduction_of_terminalCalibration
    {iota : Type*} [Fintype iota] [Nonempty iota]
    (left right targetRadius : iota → ℝ)
    {k a xMinus xPlus sigmaMinus sigmaPlus Ceff M0 L R0 : ℝ}
    (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    (hxMinus : xMinus < a) (hxPlus : xPlus < a)
    (hsigmaMinus : 0 < sigmaMinus) (hsigmaPlus : 0 < sigmaPlus)
    (hleft : ∀ i, 0 ≤ left i) (hlr : ∀ i, left i < right i)
    (hright : ∀ i, right i ≤ Real.pi)
    (hTargetRadius : ∀ i, 0 < targetRadius i)
    (hAdjointMassSum :
      ∑ i, platformAdjointIntervalMass
        a xMinus xPlus sigmaMinus sigmaPlus (left i) (right i) = R0)
    (hcert : PlatformTerminalCalibration
      k a xMinus xPlus sigmaMinus sigmaPlus Ceff)
    (hcalibration :
      M0 + (Ceff - platformPotentialConstant k a) * R0 = L) :
    L < M0 + ∑ i, blockRadiusExpression
      (platformReferenceIntervalMass k a (left i) (right i))
      (platformAdjointIntervalMass a xMinus xPlus
        sigmaMinus sigmaPlus (left i) (right i))
      (platformPotentialConstant k a)
      (platformDeficitBlockEnergy k a xMinus xPlus
        sigmaMinus sigmaPlus (left i) (right i))
      (targetRadius i) := by
  apply finite_platformDeficitBlock_strict_reduction
    left right targetRadius hk ha ha2 hthreshold hxMinus hxPlus
      hsigmaMinus hsigmaPlus hleft hlr hright hTargetRadius
      hAdjointMassSum
  · intro i
    exact platformCircleBlockMargin_pos_of_terminalCalibration
      hk ha ha2 hthreshold hxMinus hxPlus hsigmaMinus hsigmaPlus
        (hleft i) (hlr i) (hright i) hcert
  · exact hcalibration

end

end Erdos1038
