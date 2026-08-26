import ErdosProblems.Erdos1038.HighKPlatformAffineCrossingSmoke
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner

/-!
# Semantic affine-corner calibration bridge

The historical affine calibration wrapper asks for an `EvalPositive`
certificate for the complete, duplicated corner expression.  Production
cells instead assemble the same positivity statement semantically from
independently checked components.  This module changes only that one input;
all crossing, cap, derivative, and real-analysis arguments are inherited
unchanged from the original calibration proof.

Keeping this bridge separate also leaves the legacy smoke module and its
monolithic executable example untouched.
-/

set_option warningAsError false

namespace Erdos1038.HighKPlatformAffineSemanticCalibration

open Erdos1038 Set RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformFormula
open Erdos1038.HighKPlatformCrossingCertificates
open Erdos1038.HighKPlatformAffineCornerComponents
open Erdos1038.HighKPlatformAffineSemanticCorner

noncomputable section

/-- Semantic-corner variant of the central affine certificate theorem. -/
theorem affineEdgeCertificate_of_uniformCorner_of_derivative
    {X : Fin 5 → RatInterval} {v : Fin 5 → ℝ}
    {logTerms sqrtSteps trigDoubles N : ℕ}
    {edge : HighKPlatformEdge} {qCap rCap : Rat}
    (hordered : ∀ i, (X i).Ordered)
    (hcontains : ∀ i, (X i).Contains (v i))
    (hN : 0 < N)
    (hpi : evalReal v piE = Real.pi)
    (hqCapPos : 0 < (qCap : ℝ)) (hqCapPi : (qCap : ℝ) ≤ Real.pi)
    (hrCapPos : 0 < (rCap : ℝ)) (hrCapPi : (rCap : ℝ) ≤ Real.pi)
    (haPi : EvalPositive X (apiE sqrtSteps edge))
    (hQmax : EvalPositive X (qmaxE sqrtSteps edge))
    (hRmax : EvalPositive X (rmaxE sqrtSteps edge))
    (hRltQ : EvalNegative X
      (.sub (rmaxE sqrtSteps edge) (qmaxE sqrtSteps edge)))
    (hQcap : EvalNegative X
      (.sub (qmaxE sqrtSteps edge) (.rat qCap)))
    (hRcap : EvalNegative X
      (.sub (rmaxE sqrtSteps edge) (.rat rCap)))
    (hCeff : EvalNegative X (ceffE logTerms sqrtSteps edge))
    (hcorner : UniformPositive X
      (affineCornerLowerE logTerms sqrtSteps trigDoubles N edge qCap rCap))
    (hderivativeNeg : ∀ Q ∈
      Ioo (evalReal v (rmaxE sqrtSteps edge))
        (evalReal v (qmaxE sqrtSteps edge)),
      affineCircleScalarDerivative
        (evalReal v (apiE sqrtSteps edge))
        (evalReal v (ceffE logTerms sqrtSteps edge))
        (evalReal v (rmaxE sqrtSteps edge)) Q < 0) :
    AffineCircleCertificate
      (evalReal v (capacityE edge))
      (evalReal v (apiE sqrtSteps edge))
      (evalReal v (bpiE sqrtSteps edge))
      (evalReal v (ceffE logTerms sqrtSteps edge))
      (evalReal v (qmaxE sqrtSteps edge))
      (evalReal v (rmaxE sqrtSteps edge)) := by
  have haPi' := evalPositive_sound hordered hcontains haPi
  have hQmax' := evalPositive_sound hordered hcontains hQmax
  have hRmax' := evalPositive_sound hordered hcontains hRmax
  have hRltQ' := evalNegative_sound hordered hcontains hRltQ
  have hQcap' := evalNegative_sound hordered hcontains hQcap
  have hRcap' := evalNegative_sound hordered hcontains hRcap
  have hCeff' := evalNegative_sound hordered hcontains hCeff
  have hcorner' := hcorner v hordered hcontains
  have hRQ : evalReal v (rmaxE sqrtSteps edge) <
      evalReal v (qmaxE sqrtSteps edge) := by
    simpa [HighKIntervalExpr.sub] using! hRltQ'
  have hQle : evalReal v (qmaxE sqrtSteps edge) ≤ (qCap : ℝ) := by
    simpa [HighKIntervalExpr.sub] using! hQcap'.le
  have hRle : evalReal v (rmaxE sqrtSteps edge) ≤ (rCap : ℝ) := by
    simpa [HighKIntervalExpr.sub] using! hRcap'.le
  have hcornerLower := affineCornerLowerE_le
    (logTerms := logTerms) (trigDoubles := trigDoubles) hN hpi
    hqCapPos hqCapPi hrCapPos hrCapPi hQmax' hRmax' hQle hRle
  have hcornerPos : 0 < affineCircleScalar
      (evalReal v (capacityE edge))
      (evalReal v (apiE sqrtSteps edge))
      (evalReal v (bpiE sqrtSteps edge))
      (evalReal v (ceffE logTerms sqrtSteps edge))
      (evalReal v (rmaxE sqrtSteps edge))
      (evalReal v (qmaxE sqrtSteps edge))
      (evalReal v (qmaxE sqrtSteps edge)) :=
    hcorner'.trans_le hcornerLower
  have hanti : AntitoneOn
      (affineCircleScalar
        (evalReal v (capacityE edge))
        (evalReal v (apiE sqrtSteps edge))
        (evalReal v (bpiE sqrtSteps edge))
        (evalReal v (ceffE logTerms sqrtSteps edge))
        (evalReal v (rmaxE sqrtSteps edge))
        (evalReal v (qmaxE sqrtSteps edge)))
      (Icc (evalReal v (rmaxE sqrtSteps edge))
        (evalReal v (qmaxE sqrtSteps edge))) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc _ _)
    · intro Q hQ
      exact (hasDerivAt_affineCircleScalar
        (hRmax'.trans_le hQ.1)).continuousAt.continuousWithinAt
    · intro Q hQ
      rw [interior_Icc] at hQ
      exact (hasDerivAt_affineCircleScalar
        (hRmax'.trans hQ.1)).hasDerivWithinAt
    · intro Q hQ
      rw [interior_Icc] at hQ
      exact (hderivativeNeg Q hQ).le
  have hleftScalar : 0 < affineCircleScalar
      (evalReal v (capacityE edge))
      (evalReal v (apiE sqrtSteps edge))
      (evalReal v (bpiE sqrtSteps edge))
      (evalReal v (ceffE logTerms sqrtSteps edge))
      (evalReal v (rmaxE sqrtSteps edge))
      (evalReal v (qmaxE sqrtSteps edge))
      (evalReal v (rmaxE sqrtSteps edge)) :=
    hcornerPos.trans_le
      (hanti ⟨le_rfl, hRQ.le⟩ ⟨hRQ.le, le_rfl⟩ hRQ.le)
  refine ⟨haPi', hRmax', hRQ, hQle.trans hqCapPi, hCeff', ?_,
    hcornerPos, hderivativeNeg⟩
  simpa [affineCircleScalar] using! hleftScalar

/-- Mixed-precision platform wrapper accepting semantic corner positivity. -/
theorem platformAffineCalibration_of_uniformCorner_mixedDerivative
    {X : Fin 5 → RatInterval} {k xm xp ell : ℝ}
    {logTerms sqrtSteps trigDoubles N : ℕ}
    {derivativeLogTerms derivativeSqrtSteps derivativeTrigDoubles : ℕ}
    {edge : HighKPlatformEdge} {qCap rCap : Rat}
    (hordered : ∀ i, (X i).Ordered)
    (hcontains : ∀ i,
      (X i).Contains (![k, xm, xp, ell, Real.pi] i))
    (hxm : xm < highKPlatformEdge edge k)
    (hxp : xp < highKPlatformEdge edge k)
    (ha2 : highKPlatformEdge edge k < 2)
    (hN : 0 < N)
    (hqCapPos : 0 < (qCap : ℝ)) (hqCapPi : (qCap : ℝ) ≤ Real.pi)
    (hrCapPos : 0 < (rCap : ℝ)) (hrCapPi : (rCap : ℝ) ≤ Real.pi)
    (haPi : EvalPositive X (apiE sqrtSteps edge))
    (hQmax : EvalPositive X (qmaxE sqrtSteps edge))
    (hRmax : EvalPositive X (rmaxE sqrtSteps edge))
    (hRltQ : EvalNegative X
      (.sub (rmaxE sqrtSteps edge) (qmaxE sqrtSteps edge)))
    (hQcap : EvalNegative X
      (.sub (qmaxE sqrtSteps edge) (.rat qCap)))
    (hRcap : EvalNegative X
      (.sub (rmaxE sqrtSteps edge) (.rat rCap)))
    (hCeff : EvalNegative X (ceffE logTerms sqrtSteps edge))
    (hcorner : UniformPositive X
      (affineCornerLowerE logTerms sqrtSteps trigDoubles N edge qCap rCap))
    (hderivative : AffineDerivativeBoxCertificate X
      derivativeLogTerms derivativeSqrtSteps derivativeTrigDoubles edge) :
    PlatformAffineCalibration k (highKPlatformEdge edge k) xm xp
      (-1 / platformExteriorWx k (highKPlatformEdge edge k) xm)
      (1 / platformExteriorWx k (highKPlatformEdge edge k) xp)
      (platformEffectiveConstant ell k (highKPlatformEdge edge k) xm xp
        (-1 / platformExteriorWx k (highKPlatformEdge edge k) xm)
        (1 / platformExteriorWx k (highKPlatformEdge edge k) xp)) := by
  let v : Fin 5 → ℝ := ![k, xm, xp, ell, Real.pi]
  have hcontains' : ∀ i, (X i).Contains (v i) := by
    simpa only [v] using! hcontains
  have hRmaxMain : 0 < evalReal v (rmaxE sqrtSteps edge) :=
    evalPositive_sound hordered hcontains' hRmax
  have hRmaxDerivative :
      0 < evalReal v (rmaxE derivativeSqrtSteps edge) := by
    rw [rmaxE_eval derivativeSqrtSteps edge hxm hxp ha2]
    rw [rmaxE_eval sqrtSteps edge hxm hxp ha2] at hRmaxMain
    exact hRmaxMain
  have hderivativeNeg : ∀ Q ∈
      Ioo (evalReal v (rmaxE sqrtSteps edge))
        (evalReal v (qmaxE sqrtSteps edge)),
      affineCircleScalarDerivative
        (evalReal v (apiE sqrtSteps edge))
        (evalReal v (ceffE logTerms sqrtSteps edge))
        (evalReal v (rmaxE sqrtSteps edge)) Q < 0 := by
    intro Q hQ
    have hQ' : Q ∈ Ioo
        (evalReal v (rmaxE derivativeSqrtSteps edge))
        (evalReal v (qmaxE derivativeSqrtSteps edge)) := by
      simpa only [apiE_eval, qmaxE_eval,
        rmaxE_eval derivativeSqrtSteps edge hxm hxp ha2,
        rmaxE_eval sqrtSteps edge hxm hxp ha2] using! hQ
    have hd := affineDerivative_neg_of_boxCertificate hderivative
      hordered hcontains' (by simp [v]) hRmaxDerivative Q hQ'
    simpa only [apiE_eval,
      ceffE_eval derivativeLogTerms derivativeSqrtSteps edge hxm hxp ha2,
      ceffE_eval logTerms sqrtSteps edge hxm hxp ha2,
      rmaxE_eval derivativeSqrtSteps edge hxm hxp ha2,
      rmaxE_eval sqrtSteps edge hxm hxp ha2] using! hd
  have hcert := affineEdgeCertificate_of_uniformCorner_of_derivative
    hordered hcontains' hN (by simp [v]) hqCapPos hqCapPi
    hrCapPos hrCapPi haPi hQmax hRmax hRltQ hQcap hRcap hCeff hcorner
    hderivativeNeg
  simpa only [v, PlatformAffineCalibration, capacityE_eval, apiE_eval,
    bpiE_eval sqrtSteps edge hxm hxp ha2,
    ceffE_eval logTerms sqrtSteps edge hxm hxp ha2,
    qmaxE_eval, rmaxE_eval sqrtSteps edge hxm hxp ha2] using! hcert

end

end Erdos1038.HighKPlatformAffineSemanticCalibration
