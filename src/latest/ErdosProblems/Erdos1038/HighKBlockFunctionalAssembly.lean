import ErdosProblems.Erdos1038.HighKResidualBlockAssembly
import ErdosProblems.Erdos1038.ResidualDeficit

/-!
# From calibrated residual blocks to the target width functional

The strict circle calibration gives a lower bound for a sum of
`blockRadiusExpression`s.  The global convex/supporting argument controls
the same sum with the explicit `2 R_i` radius terms removed.  This file
performs that final algebra exactly, so the remaining analytic statement is
the genuine supporting bound and not a mixture of support, block geometry,
and radius bookkeeping.
-/

set_option warningAsError false

open scoped BigOperators

namespace Erdos1038

noncomputable section

variable {ι : Type*} [Fintype ι] [LinearOrder ι]

/-- The contribution of one canonical target block before the local
component radius `2 R_i` is added.  This is the brace in manuscript
equation `(4.29)` without its final `2 R_i`. -/
def platformResidualTangentBlockTerm
    (C : ResidualConfiguration ι)
    (k a xMinus xPlus sigmaMinus sigmaPlus : ℝ)
    (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a) (i : ι) : ℝ :=
  let left := platformResidualBlockLeft C k a hk ha ha2 hthreshold i
  let right := platformResidualBlockRight C k a hk ha ha2 hthreshold i
  platformAdjointIntervalMass
      a xMinus xPlus sigmaMinus sigmaPlus left right *
      (-C.weight i * Real.log (residualRadius C k i) -
        platformPotentialConstant k a - C.weight i) +
    platformDeficitBlockEnergy
      k a xMinus xPlus sigmaMinus sigmaPlus left right

/-- Exact global statement supplied by the convex supporting inequality,
the endpoint-corrected adjoint identity, and the block tangent estimate.
It is deliberately phrased with the concrete canonical platform blocks. -/
def PlatformResidualSupportingBound
    (C : ResidualConfiguration ι)
    (k a xMinus xPlus sigmaMinus sigmaPlus : ℝ)
    (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    (M0 targetWidth : ℝ) : Prop :=
  M0 + ∑ i, platformResidualTangentBlockTerm C k a
      xMinus xPlus sigmaMinus sigmaPlus hk ha ha2 hthreshold i ≤
    targetWidth

omit [LinearOrder ι] in
/-- Equation `(2.9)` in the exact form used by the block tangent
calculation: the target external field and all off-diagonal target
interactions equal `-q_i log R_i`. -/
theorem neg_weight_mul_log_residualRadius_eq_background
    (C : ResidualConfiguration ι) (k : ℝ) (i : ι) :
    -C.weight i * Real.log (residualRadius C k i) =
      residualBackgroundAt C k i := by
  rw [log_residualRadius]
  field_simp [(C.weight_pos i).ne']

/-- Semantic form of one tangent block after substituting the exact target
radius identity. -/
theorem platformResidualTangentBlockTerm_eq_background
    (C : ResidualConfiguration ι)
    (k a xMinus xPlus sigmaMinus sigmaPlus : ℝ)
    (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a) (i : ι) :
    platformResidualTangentBlockTerm C k a
        xMinus xPlus sigmaMinus sigmaPlus hk ha ha2 hthreshold i =
      let left := platformResidualBlockLeft C k a hk ha ha2 hthreshold i
      let right := platformResidualBlockRight C k a hk ha ha2 hthreshold i
      platformAdjointIntervalMass
          a xMinus xPlus sigmaMinus sigmaPlus left right *
          (residualBackgroundAt C k i -
            platformPotentialConstant k a - C.weight i) +
        platformDeficitBlockEnergy
          k a xMinus xPlus sigmaMinus sigmaPlus left right := by
  unfold platformResidualTangentBlockTerm
  rw [neg_weight_mul_log_residualRadius_eq_background]

theorem blockRadiusExpression_eq_tangentBlockTerm_add_radius
    (C : ResidualConfiguration ι)
    (k a xMinus xPlus sigmaMinus sigmaPlus : ℝ)
    (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a) (i : ι) :
    blockRadiusExpression
        (C.weight i)
        (platformAdjointIntervalMass a xMinus xPlus sigmaMinus sigmaPlus
          (platformResidualBlockLeft C k a hk ha ha2 hthreshold i)
          (platformResidualBlockRight C k a hk ha ha2 hthreshold i))
        (platformPotentialConstant k a)
        (platformDeficitBlockEnergy k a xMinus xPlus sigmaMinus sigmaPlus
          (platformResidualBlockLeft C k a hk ha ha2 hthreshold i)
          (platformResidualBlockRight C k a hk ha ha2 hthreshold i))
        (residualRadius C k i) =
      platformResidualTangentBlockTerm C k a
          xMinus xPlus sigmaMinus sigmaPlus hk ha ha2 hthreshold i +
        2 * residualRadius C k i := by
  rfl

/-- The calibrated block sum splits exactly into the supporting tangent
sum and twice the total residual radius. -/
theorem sum_blockRadiusExpression_eq_tangent_add_twice_radiusSum
    (C : ResidualConfiguration ι)
    (k a xMinus xPlus sigmaMinus sigmaPlus M0 : ℝ)
    (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a) :
    M0 + ∑ i, blockRadiusExpression
        (C.weight i)
        (platformAdjointIntervalMass a xMinus xPlus sigmaMinus sigmaPlus
          (platformResidualBlockLeft C k a hk ha ha2 hthreshold i)
          (platformResidualBlockRight C k a hk ha ha2 hthreshold i))
        (platformPotentialConstant k a)
        (platformDeficitBlockEnergy k a xMinus xPlus sigmaMinus sigmaPlus
          (platformResidualBlockLeft C k a hk ha ha2 hthreshold i)
          (platformResidualBlockRight C k a hk ha ha2 hthreshold i))
        (residualRadius C k i) =
      (M0 + ∑ i, platformResidualTangentBlockTerm C k a
        xMinus xPlus sigmaMinus sigmaPlus hk ha ha2 hthreshold i) +
        2 * residualRadiusSum C k := by
  simp_rw [blockRadiusExpression_eq_tangentBlockTerm_add_radius
    C k a xMinus xPlus sigmaMinus sigmaPlus hk ha ha2 hthreshold]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  unfold residualRadiusSum
  ring

/-- A strict calibrated block lower bound plus the genuine supporting
bound yields the exact target functional `width + 2 * radiusSum`. -/
theorem orderedResidual_functional_strict_of_margin
    (C : ResidualConfiguration ι)
    {k a xMinus xPlus sigmaMinus sigmaPlus Ceff M0 L targetWidth : ℝ}
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
          platformAdjointMass a xMinus xPlus sigmaMinus sigmaPlus = L)
    (hsupport : PlatformResidualSupportingBound C k a
      xMinus xPlus sigmaMinus sigmaPlus hk ha ha2 hthreshold
      M0 targetWidth) :
    L < targetWidth + 2 * residualRadiusSum C k := by
  have hstrict := orderedResidual_platformDeficitBlock_strict_reduction C
    hk ha ha2 hthreshold hxMinus hxPlus hsigmaMinus hsigmaPlus
      hmargin hcalibration
  rw [sum_blockRadiusExpression_eq_tangent_add_twice_radiusSum
    C k a xMinus xPlus sigmaMinus sigmaPlus M0
      hk ha ha2 hthreshold] at hstrict
  unfold PlatformResidualSupportingBound at hsupport
  have hle :
      (M0 + ∑ i, platformResidualTangentBlockTerm C k a
          xMinus xPlus sigmaMinus sigmaPlus hk ha ha2 hthreshold i) +
          2 * residualRadiusSum C k ≤
        targetWidth + 2 * residualRadiusSum C k := by
    linarith
  exact hstrict.trans_le hle

/-- Constant-edge specialization. -/
theorem orderedResidual_functional_strict_of_constantEdgeCalibration
    (C : ResidualConfiguration ι)
    {k a xMinus xPlus sigmaMinus sigmaPlus Ceff M0 L targetWidth : ℝ}
    (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    (hxMinus : xMinus < a) (hxPlus : xPlus < a)
    (hsigmaMinus : 0 < sigmaMinus) (hsigmaPlus : 0 < sigmaPlus)
    (hcert : PlatformConstantEdgeCalibration
      k a xMinus xPlus sigmaMinus sigmaPlus Ceff)
    (hcalibration :
      M0 + (Ceff - platformPotentialConstant k a) *
          platformAdjointMass a xMinus xPlus sigmaMinus sigmaPlus = L)
    (hsupport : PlatformResidualSupportingBound C k a
      xMinus xPlus sigmaMinus sigmaPlus hk ha ha2 hthreshold
      M0 targetWidth) :
    L < targetWidth + 2 * residualRadiusSum C k := by
  apply orderedResidual_functional_strict_of_margin C
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
  · exact hsupport

/-- Affine-edge specialization. -/
theorem orderedResidual_functional_strict_of_affineCalibration
    (C : ResidualConfiguration ι)
    {k a xMinus xPlus sigmaMinus sigmaPlus Ceff M0 L targetWidth : ℝ}
    (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    (hxMinus : xMinus < a) (hxPlus : xPlus < a)
    (hsigmaMinus : 0 < sigmaMinus) (hsigmaPlus : 0 < sigmaPlus)
    (hcert : PlatformAffineCalibration
      k a xMinus xPlus sigmaMinus sigmaPlus Ceff)
    (hcalibration :
      M0 + (Ceff - platformPotentialConstant k a) *
          platformAdjointMass a xMinus xPlus sigmaMinus sigmaPlus = L)
    (hsupport : PlatformResidualSupportingBound C k a
      xMinus xPlus sigmaMinus sigmaPlus hk ha ha2 hthreshold
      M0 targetWidth) :
    L < targetWidth + 2 * residualRadiusSum C k := by
  apply orderedResidual_functional_strict_of_margin C
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
  · exact hsupport

/-- Terminal specialization. -/
theorem orderedResidual_functional_strict_of_terminalCalibration
    (C : ResidualConfiguration ι)
    {k a xMinus xPlus sigmaMinus sigmaPlus Ceff M0 L targetWidth : ℝ}
    (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    (hxMinus : xMinus < a) (hxPlus : xPlus < a)
    (hsigmaMinus : 0 < sigmaMinus) (hsigmaPlus : 0 < sigmaPlus)
    (hcert : PlatformTerminalCalibration
      k a xMinus xPlus sigmaMinus sigmaPlus Ceff)
    (hcalibration :
      M0 + (Ceff - platformPotentialConstant k a) *
          platformAdjointMass a xMinus xPlus sigmaMinus sigmaPlus = L)
    (hsupport : PlatformResidualSupportingBound C k a
      xMinus xPlus sigmaMinus sigmaPlus hk ha ha2 hthreshold
      M0 targetWidth) :
    L < targetWidth + 2 * residualRadiusSum C k := by
  apply orderedResidual_functional_strict_of_margin C
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
  · exact hsupport

end

end Erdos1038
