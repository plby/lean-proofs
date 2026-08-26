import ErdosProblems.Erdos1038.HighKBlockFunctionalAssembly
import ErdosProblems.Erdos1038.HighKPlatformIntervalFormula
import ErdosProblems.Erdos1038.Definitions

/-!
# Effective-constant assembly for the high-ratio platform argument

The interval verifier uses `platformEffectiveConstant`, obtained by solving
the scalar mass calibration for the prescribed lower target `L`.  This file
proves that calibration exactly and packages the three scalar certificate
interfaces directly as strict bounds for the normalized residual functional.
-/

set_option warningAsError false

namespace Erdos1038

noncomputable section

variable {ι : Type*} [Fintype ι] [LinearOrder ι]

/-- The definition of the effective constant is the exact solution of the
adjoint-mass calibration equation whenever the adjoint mass is nonzero. -/
theorem platformEffectiveConstant_calibration
    {ell k a xMinus xPlus sigmaMinus sigmaPlus : ℝ}
    (hmass : platformAdjointMass a xMinus xPlus
      sigmaMinus sigmaPlus ≠ 0) :
    (xPlus - xMinus) +
        (platformEffectiveConstant ell k a xMinus xPlus
            sigmaMinus sigmaPlus - platformPotentialConstant k a) *
          platformAdjointMass a xMinus xPlus sigmaMinus sigmaPlus = ell := by
  unfold platformEffectiveConstant
  field_simp [hmass]
  ring

/-- Positive crossing weights make the effective-constant calibration
automatic. -/
theorem platformEffectiveConstant_calibration_of_pos
    {ell k a xMinus xPlus sigmaMinus sigmaPlus : ℝ}
    (hxMinus : xMinus < a) (hxPlus : xPlus < a)
    (hsigmaMinus : 0 < sigmaMinus) (hsigmaPlus : 0 < sigmaPlus)
    (ha2 : a < 2) :
    (xPlus - xMinus) +
        (platformEffectiveConstant ell k a xMinus xPlus
            sigmaMinus sigmaPlus - platformPotentialConstant k a) *
          platformAdjointMass a xMinus xPlus sigmaMinus sigmaPlus = ell := by
  apply platformEffectiveConstant_calibration
  exact (platformAdjointMass_pos hxMinus hxPlus
    hsigmaMinus hsigmaPlus ha2).ne'

/-- An affine-edge scalar certificate, with the verifier's effective
constant, closes the strict residual functional once the canonical support
bound is available. -/
theorem orderedResidual_functional_strict_of_affineEffectiveCalibration
    (C : ResidualConfiguration ι)
    {k a xMinus xPlus sigmaMinus sigmaPlus targetWidth : ℝ}
    (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    (hxMinus : xMinus < a) (hxPlus : xPlus < a)
    (hsigmaMinus : 0 < sigmaMinus) (hsigmaPlus : 0 < sigmaPlus)
    (hcert : PlatformAffineCalibration k a xMinus xPlus
      sigmaMinus sigmaPlus
      (platformEffectiveConstant L k a xMinus xPlus
        sigmaMinus sigmaPlus))
    (hsupport : PlatformResidualSupportingBound C k a
      xMinus xPlus sigmaMinus sigmaPlus hk ha ha2 hthreshold
      (xPlus - xMinus) targetWidth) :
    L < targetWidth + 2 * residualRadiusSum C k := by
  apply orderedResidual_functional_strict_of_affineCalibration C
    hk ha ha2 hthreshold hxMinus hxPlus hsigmaMinus hsigmaPlus hcert
  · exact platformEffectiveConstant_calibration_of_pos
      hxMinus hxPlus hsigmaMinus hsigmaPlus ha2
  · exact hsupport

/-- Constant-edge counterpart of
`orderedResidual_functional_strict_of_affineEffectiveCalibration`. -/
theorem orderedResidual_functional_strict_of_constantEffectiveCalibration
    (C : ResidualConfiguration ι)
    {k a xMinus xPlus sigmaMinus sigmaPlus targetWidth : ℝ}
    (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    (hxMinus : xMinus < a) (hxPlus : xPlus < a)
    (hsigmaMinus : 0 < sigmaMinus) (hsigmaPlus : 0 < sigmaPlus)
    (hcert : PlatformConstantEdgeCalibration k a xMinus xPlus
      sigmaMinus sigmaPlus
      (platformEffectiveConstant L k a xMinus xPlus
        sigmaMinus sigmaPlus))
    (hsupport : PlatformResidualSupportingBound C k a
      xMinus xPlus sigmaMinus sigmaPlus hk ha ha2 hthreshold
      (xPlus - xMinus) targetWidth) :
    L < targetWidth + 2 * residualRadiusSum C k := by
  apply orderedResidual_functional_strict_of_constantEdgeCalibration C
    hk ha ha2 hthreshold hxMinus hxPlus hsigmaMinus hsigmaPlus hcert
  · exact platformEffectiveConstant_calibration_of_pos
      hxMinus hxPlus hsigmaMinus hsigmaPlus ha2
  · exact hsupport

/-- Terminal counterpart of the effective-constant assembly. -/
theorem orderedResidual_functional_strict_of_terminalEffectiveCalibration
    (C : ResidualConfiguration ι)
    {k a xMinus xPlus sigmaMinus sigmaPlus targetWidth : ℝ}
    (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    (hxMinus : xMinus < a) (hxPlus : xPlus < a)
    (hsigmaMinus : 0 < sigmaMinus) (hsigmaPlus : 0 < sigmaPlus)
    (hcert : PlatformTerminalCalibration k a xMinus xPlus
      sigmaMinus sigmaPlus
      (platformEffectiveConstant L k a xMinus xPlus
        sigmaMinus sigmaPlus))
    (hsupport : PlatformResidualSupportingBound C k a
      xMinus xPlus sigmaMinus sigmaPlus hk ha ha2 hthreshold
      (xPlus - xMinus) targetWidth) :
    L < targetWidth + 2 * residualRadiusSum C k := by
  apply orderedResidual_functional_strict_of_terminalCalibration C
    hk ha ha2 hthreshold hxMinus hxPlus hsigmaMinus hsigmaPlus hcert
  · exact platformEffectiveConstant_calibration_of_pos
      hxMinus hxPlus hsigmaMinus hsigmaPlus ha2
  · exact hsupport

/-- Unified scalar certificate used by the final regime split.  Each branch
has already been reduced to the same effective constant and therefore to the
same normalized residual functional. -/
def PlatformEffectiveCalibration
    (k a xMinus xPlus sigmaMinus sigmaPlus : ℝ) : Prop :=
  PlatformAffineCalibration k a xMinus xPlus sigmaMinus sigmaPlus
      (platformEffectiveConstant L k a xMinus xPlus
        sigmaMinus sigmaPlus) ∨
    PlatformConstantEdgeCalibration k a xMinus xPlus
      sigmaMinus sigmaPlus
      (platformEffectiveConstant L k a xMinus xPlus
        sigmaMinus sigmaPlus) ∨
    PlatformTerminalCalibration k a xMinus xPlus sigmaMinus sigmaPlus
      (platformEffectiveConstant L k a xMinus xPlus
        sigmaMinus sigmaPlus)

/-- Any of the three certified scalar regimes gives the same strict target
functional once canonical support is known. -/
theorem orderedResidual_functional_strict_of_effectiveCalibration
    (C : ResidualConfiguration ι)
    {k a xMinus xPlus sigmaMinus sigmaPlus targetWidth : ℝ}
    (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    (hxMinus : xMinus < a) (hxPlus : xPlus < a)
    (hsigmaMinus : 0 < sigmaMinus) (hsigmaPlus : 0 < sigmaPlus)
    (hcert : PlatformEffectiveCalibration k a xMinus xPlus
      sigmaMinus sigmaPlus)
    (hsupport : PlatformResidualSupportingBound C k a
      xMinus xPlus sigmaMinus sigmaPlus hk ha ha2 hthreshold
      (xPlus - xMinus) targetWidth) :
    L < targetWidth + 2 * residualRadiusSum C k := by
  rcases hcert with hcert | hcert | hcert
  · exact orderedResidual_functional_strict_of_affineEffectiveCalibration C
      hk ha ha2 hthreshold hxMinus hxPlus hsigmaMinus hsigmaPlus
        hcert hsupport
  · exact orderedResidual_functional_strict_of_constantEffectiveCalibration C
      hk ha ha2 hthreshold hxMinus hxPlus hsigmaMinus hsigmaPlus
        hcert hsupport
  · exact orderedResidual_functional_strict_of_terminalEffectiveCalibration C
      hk ha ha2 hthreshold hxMinus hxPlus hsigmaMinus hsigmaPlus
        hcert hsupport

end

end Erdos1038
