import ErdosProblems.Erdos1038.HighKPlatformDeficitAssembly
import ErdosProblems.Erdos1038.PlatformAdjointPartition
import ErdosProblems.Erdos1038.ResidualRadius

/-!
# Strict platform assembly for an ordered residual configuration

The inverse reference CDF assigns one consecutive angular block to every
atom of an ordered residual configuration.  This file specializes the
finite platform-deficit assembly to those canonical blocks.  Thus the
reference block mass is the atom weight, the adjoint block masses telescope
to the full adjoint mass, and the target radius is the residual radius.
-/

set_option warningAsError false

open Set
open scoped BigOperators

namespace Erdos1038

noncomputable section

variable {ι : Type*} [Fintype ι] [LinearOrder ι]

/-- The strict concrete deficit-energy reduction on the canonical blocks of
an ordered residual configuration.  All partition geometry, reference-mass
identities, adjoint-mass telescoping, and target-radius positivity are
discharged internally. -/
theorem orderedResidual_platformDeficitBlock_strict_reduction
    (C : ResidualConfiguration ι)
    {k a xMinus xPlus sigmaMinus sigmaPlus Ceff M0 L : ℝ}
    (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    (hxMinus : xMinus < a) (hxPlus : xPlus < a)
    (hsigmaMinus : 0 < sigmaMinus) (hsigmaPlus : 0 < sigmaPlus)
    (hmargin : ∀ i, 0 < circleBlockMargin
      (platformCapacity a) (platformAPi k a)
      (platformBPi a xMinus xPlus sigmaMinus sigmaPlus) Ceff
      (platformReferenceCircleRadius k a
        (platformResidualBlockLeft C k a hk ha ha2 hthreshold i)
        (platformResidualBlockRight C k a hk ha ha2 hthreshold i))
      (platformAdjointCircleRadius a xMinus xPlus sigmaMinus sigmaPlus
        (platformResidualBlockLeft C k a hk ha ha2 hthreshold i)
        (platformResidualBlockRight C k a hk ha ha2 hthreshold i)))
    (hcalibration :
      M0 + (Ceff - platformPotentialConstant k a) *
          platformAdjointMass a xMinus xPlus sigmaMinus sigmaPlus = L) :
    L < M0 + ∑ i, blockRadiusExpression
      (C.weight i)
      (platformAdjointIntervalMass a xMinus xPlus sigmaMinus sigmaPlus
        (platformResidualBlockLeft C k a hk ha ha2 hthreshold i)
        (platformResidualBlockRight C k a hk ha ha2 hthreshold i))
      (platformPotentialConstant k a)
      (platformDeficitBlockEnergy k a xMinus xPlus sigmaMinus sigmaPlus
        (platformResidualBlockLeft C k a hk ha ha2 hthreshold i)
        (platformResidualBlockRight C k a hk ha ha2 hthreshold i))
      (residualRadius C k i) := by
  classical
  have hindex : (Finset.univ : Finset ι).Nonempty := by
    apply Finset.nonempty_of_sum_ne_zero (f := C.weight)
    simp [C.sum_weight]
  letI : Nonempty ι := hindex.to_type
  have hstrict := finite_platformDeficitBlock_strict_reduction
    (fun i ↦ platformResidualBlockLeft C k a hk ha ha2 hthreshold i)
    (fun i ↦ platformResidualBlockRight C k a hk ha ha2 hthreshold i)
    (fun i ↦ residualRadius C k i)
    hk ha ha2 hthreshold hxMinus hxPlus hsigmaMinus hsigmaPlus
    (fun i ↦ (platformResidualBlockLeft_mem_Icc
      C k a hk ha ha2 hthreshold i).1)
    (fun i ↦ platformResidualBlockLeft_lt_right
      C k a hk ha ha2 hthreshold i)
    (fun i ↦ (platformResidualBlockRight_mem_Icc
      C k a hk ha ha2 hthreshold i).2)
    (fun i ↦ residualRadius_pos C k i)
    (sum_platformAdjointIntervalMass_residualBlocks
      C k a hk ha ha2 hthreshold xMinus xPlus sigmaMinus sigmaPlus
        hxMinus hxPlus)
    hmargin hcalibration
  simpa only [platformReferenceIntervalMass_residualBlock] using! hstrict

/-- A constant-edge scalar certificate supplies every canonical residual
block margin. -/
theorem orderedResidual_platformDeficitBlock_strict_reduction_of_constantEdgeCalibration
    (C : ResidualConfiguration ι)
    {k a xMinus xPlus sigmaMinus sigmaPlus Ceff M0 L : ℝ}
    (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    (hxMinus : xMinus < a) (hxPlus : xPlus < a)
    (hsigmaMinus : 0 < sigmaMinus) (hsigmaPlus : 0 < sigmaPlus)
    (hcert : PlatformConstantEdgeCalibration
      k a xMinus xPlus sigmaMinus sigmaPlus Ceff)
    (hcalibration :
      M0 + (Ceff - platformPotentialConstant k a) *
          platformAdjointMass a xMinus xPlus sigmaMinus sigmaPlus = L) :
    L < M0 + ∑ i, blockRadiusExpression
      (C.weight i)
      (platformAdjointIntervalMass a xMinus xPlus sigmaMinus sigmaPlus
        (platformResidualBlockLeft C k a hk ha ha2 hthreshold i)
        (platformResidualBlockRight C k a hk ha ha2 hthreshold i))
      (platformPotentialConstant k a)
      (platformDeficitBlockEnergy k a xMinus xPlus sigmaMinus sigmaPlus
        (platformResidualBlockLeft C k a hk ha ha2 hthreshold i)
        (platformResidualBlockRight C k a hk ha ha2 hthreshold i))
      (residualRadius C k i) := by
  apply orderedResidual_platformDeficitBlock_strict_reduction C
    hk ha ha2 hthreshold hxMinus hxPlus hsigmaMinus hsigmaPlus
  · intro i
    exact platformCircleBlockMargin_pos_of_constantEdgeCalibration
      hk ha ha2 hthreshold hxMinus hxPlus hsigmaMinus hsigmaPlus
      (platformResidualBlockLeft_mem_Icc
        C k a hk ha ha2 hthreshold i).1
      (platformResidualBlockLeft_lt_right
        C k a hk ha ha2 hthreshold i)
      (platformResidualBlockRight_mem_Icc
        C k a hk ha ha2 hthreshold i).2 hcert
  · exact hcalibration

/-- An affine scalar certificate supplies every canonical residual block
margin. -/
theorem orderedResidual_platformDeficitBlock_strict_reduction_of_affineCalibration
    (C : ResidualConfiguration ι)
    {k a xMinus xPlus sigmaMinus sigmaPlus Ceff M0 L : ℝ}
    (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    (hxMinus : xMinus < a) (hxPlus : xPlus < a)
    (hsigmaMinus : 0 < sigmaMinus) (hsigmaPlus : 0 < sigmaPlus)
    (hcert : PlatformAffineCalibration
      k a xMinus xPlus sigmaMinus sigmaPlus Ceff)
    (hcalibration :
      M0 + (Ceff - platformPotentialConstant k a) *
          platformAdjointMass a xMinus xPlus sigmaMinus sigmaPlus = L) :
    L < M0 + ∑ i, blockRadiusExpression
      (C.weight i)
      (platformAdjointIntervalMass a xMinus xPlus sigmaMinus sigmaPlus
        (platformResidualBlockLeft C k a hk ha ha2 hthreshold i)
        (platformResidualBlockRight C k a hk ha ha2 hthreshold i))
      (platformPotentialConstant k a)
      (platformDeficitBlockEnergy k a xMinus xPlus sigmaMinus sigmaPlus
        (platformResidualBlockLeft C k a hk ha ha2 hthreshold i)
        (platformResidualBlockRight C k a hk ha ha2 hthreshold i))
      (residualRadius C k i) := by
  apply orderedResidual_platformDeficitBlock_strict_reduction C
    hk ha ha2 hthreshold hxMinus hxPlus hsigmaMinus hsigmaPlus
  · intro i
    exact platformCircleBlockMargin_pos_of_affineCalibration
      hk ha ha2 hthreshold hxMinus hxPlus hsigmaMinus hsigmaPlus
      (platformResidualBlockLeft_mem_Icc
        C k a hk ha ha2 hthreshold i).1
      (platformResidualBlockLeft_lt_right
        C k a hk ha ha2 hthreshold i)
      (platformResidualBlockRight_mem_Icc
        C k a hk ha ha2 hthreshold i).2 hcert
  · exact hcalibration

/-- A terminal scalar certificate supplies every canonical residual block
margin. -/
theorem orderedResidual_platformDeficitBlock_strict_reduction_of_terminalCalibration
    (C : ResidualConfiguration ι)
    {k a xMinus xPlus sigmaMinus sigmaPlus Ceff M0 L : ℝ}
    (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    (hxMinus : xMinus < a) (hxPlus : xPlus < a)
    (hsigmaMinus : 0 < sigmaMinus) (hsigmaPlus : 0 < sigmaPlus)
    (hcert : PlatformTerminalCalibration
      k a xMinus xPlus sigmaMinus sigmaPlus Ceff)
    (hcalibration :
      M0 + (Ceff - platformPotentialConstant k a) *
          platformAdjointMass a xMinus xPlus sigmaMinus sigmaPlus = L) :
    L < M0 + ∑ i, blockRadiusExpression
      (C.weight i)
      (platformAdjointIntervalMass a xMinus xPlus sigmaMinus sigmaPlus
        (platformResidualBlockLeft C k a hk ha ha2 hthreshold i)
        (platformResidualBlockRight C k a hk ha ha2 hthreshold i))
      (platformPotentialConstant k a)
      (platformDeficitBlockEnergy k a xMinus xPlus sigmaMinus sigmaPlus
        (platformResidualBlockLeft C k a hk ha ha2 hthreshold i)
        (platformResidualBlockRight C k a hk ha ha2 hthreshold i))
      (residualRadius C k i) := by
  apply orderedResidual_platformDeficitBlock_strict_reduction C
    hk ha ha2 hthreshold hxMinus hxPlus hsigmaMinus hsigmaPlus
  · intro i
    exact platformCircleBlockMargin_pos_of_terminalCalibration
      hk ha ha2 hthreshold hxMinus hxPlus hsigmaMinus hsigmaPlus
      (platformResidualBlockLeft_mem_Icc
        C k a hk ha ha2 hthreshold i).1
      (platformResidualBlockLeft_lt_right
        C k a hk ha ha2 hthreshold i)
      (platformResidualBlockRight_mem_Icc
        C k a hk ha ha2 hthreshold i).2 hcert
  · exact hcalibration

end

end Erdos1038
