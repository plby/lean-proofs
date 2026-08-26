import ErdosProblems.Erdos1038.HighKPlatformFunctionalAssembly
import ErdosProblems.Erdos1038.PlatformReferenceExteriorCrossingBridge

/-!
# Transport of explicit high-k calibration to canonical adjoint weights

The interval verifier uses the transparent reciprocal slopes `-1 / Wₓ` and
`1 / Wₓ`.  The canonical mesh argument names the same quantities through
the continuum reference derivative.  This file performs that exact rewrite
once for all three scalar regimes.
-/

set_option warningAsError false

namespace Erdos1038

noncomputable section

variable {iota : Type*} [Fintype iota] [LinearOrder iota]

/-- Rewrite an effective calibration proved with the checker's explicit
weights into the canonical reference-weight notation. -/
theorem PlatformExplicitExteriorCrossingCertificate.effectiveCalibration_toCanonical
    {k a xMinus xPlus : ℝ}
    (hcrossing : PlatformExplicitExteriorCrossingCertificate
      k a xMinus xPlus)
    (C : ResidualConfiguration iota)
    (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    (hcalibration : PlatformEffectiveCalibration k a xMinus xPlus
      (-1 / platformExteriorWx k a xMinus)
      (1 / platformExteriorWx k a xPlus)) :
    PlatformEffectiveCalibration k a xMinus xPlus
      (platformReferenceNegativeCrossingAdjointWeight C k a
        hk ha ha2 hthreshold xMinus)
      (platformReferencePositiveCrossingAdjointWeight C k a
        hk ha ha2 hthreshold xPlus) := by
  have hminus :
      platformReferenceNegativeCrossingAdjointWeight C k a
          hk ha ha2 hthreshold xMinus =
        -1 / platformExteriorWx k a xMinus :=
    platformReferenceNegativeCrossingAdjointWeight_eq_neg_one_div_platformExteriorWx
      C k a hk ha ha2 hthreshold
        (hcrossing.xMinus_neg.trans ha) hcrossing.xMinus_neg.ne
  have hplus :
      platformReferencePositiveCrossingAdjointWeight C k a
          hk ha ha2 hthreshold xPlus =
        1 / platformExteriorWx k a xPlus :=
    platformReferencePositiveCrossingAdjointWeight_eq_one_div_platformExteriorWx
      C k a hk ha ha2 hthreshold hcrossing.xPlus_lt_platform
        hcrossing.xPlus_pos.ne'
  simpa only [hminus, hplus] using! hcalibration

end

end Erdos1038
