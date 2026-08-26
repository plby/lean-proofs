import ErdosProblems.Erdos1038.PlatformAdjointAbelExterior

/-!
# The endpoint-corrected platform adjoint at an interior Abel parameter

Passing the exact finite-polynomial identity through the three independently
verified limits (exterior crossings, adjoint pairing, and endpoint value)
gives the complete identity for every `|lambda| < 1`.
-/

set_option warningAsError false

open Filter MeasureTheory Set
open scoped BigOperators Topology

namespace Erdos1038

noncomputable section

lemma one_div_pi_mul_integral_platformDensity_finiteAbelTransform_eq_endpoint
    {a xMinus xPlus sigmaMinus sigmaPlus : ℝ}
    (hxMinus : xMinus < a) (hxPlus : xPlus < a) (ha2 : a < 2)
    (coefficient : ℕ → ℝ) (lambda : ℝ) (N : ℕ) :
    (1 / Real.pi) *
        (∫ theta in 0..Real.pi,
          platformAngularAdjointDensity
              a xMinus xPlus sigmaMinus sigmaPlus theta *
            platformAbelFiniteHilbertTransform
              (platformRadius a) coefficient lambda N theta) =
      (1 / Real.pi) *
        (∫ theta in 0..Real.pi,
          endpointAdjointAngularDensity sigmaMinus sigmaPlus
              (platformRho a xMinus) (platformRho a xPlus) theta *
            platformAbelFiniteHilbertTransform
              (platformRadius a) coefficient lambda N theta) := by
  congr 1
  apply intervalIntegral.integral_congr
  intro theta htheta
  rw [uIcc_of_le Real.pi_pos.le] at htheta
  change platformAngularAdjointDensity
        a xMinus xPlus sigmaMinus sigmaPlus theta *
      platformAbelFiniteHilbertTransform
        (platformRadius a) coefficient lambda N theta =
    endpointAdjointAngularDensity sigmaMinus sigmaPlus
        (platformRho a xMinus) (platformRho a xPlus) theta *
      platformAbelFiniteHilbertTransform
        (platformRadius a) coefficient lambda N theta
  rw [endpointAdjointAngularDensity_platformRho_eq
    hxMinus hxPlus ha2 htheta]

theorem tendsto_one_div_pi_mul_integral_platformDensity_finiteAbelTransform
    {a xMinus xPlus sigmaMinus sigmaPlus : ℝ}
    (hxMinus : xMinus < a) (hxPlus : xPlus < a) (ha2 : a < 2)
    {coefficient : ℕ → ℝ} {lambda C : ℝ}
    (hlambda : |lambda| < 1)
    (hbound : RealSequenceBoundedBy coefficient C) :
    Tendsto
      (fun N ↦ (1 / Real.pi) *
        (∫ theta in 0..Real.pi,
          platformAngularAdjointDensity
              a xMinus xPlus sigmaMinus sigmaPlus theta *
            platformAbelFiniteHilbertTransform
              (platformRadius a) coefficient lambda N theta))
      atTop
      (nhds (platformAbelAdjointPairingSeries (platformRadius a)
        sigmaMinus sigmaPlus (platformRho a xMinus)
          (platformRho a xPlus) coefficient lambda)) := by
  have hrhoMinus := platformRho_mem_Ioo hxMinus ha2
  have hrhoPlus := platformRho_mem_Ioo hxPlus ha2
  have hendpoint :=
    tendsto_one_div_pi_mul_integral_endpointAdjointDensity_finiteAbelTransform
      (r := platformRadius a) (sigmaMinus := sigmaMinus)
      (sigmaPlus := sigmaPlus) hrhoMinus.1.le hrhoMinus.2
        hrhoPlus.1.le hrhoPlus.2 hlambda hbound
  apply hendpoint.congr'
  exact Eventually.of_forall fun N ↦
    (one_div_pi_mul_integral_platformDensity_finiteAbelTransform_eq_endpoint
      hxMinus hxPlus ha2 coefficient lambda N).symm

/-- Exact endpoint-corrected adjoint identity for every interior Abel
parameter.  Both integrals are the actual spatial/platform expressions. -/
theorem platformAbelExteriorVariation_sub_platformAdjointPairing
    {a xMinus xPlus sigmaMinus sigmaPlus : ℝ}
    (hxMinus : xMinus < a) (hxPlus : xPlus < a) (ha2 : a < 2)
    {coefficient : ℕ → ℝ} {lambda C : ℝ}
    (hlambda : |lambda| < 1)
    (hbound : RealSequenceBoundedBy coefficient C)
    (f0 : ℝ) :
    platformAbelExteriorVariation a xMinus xPlus
        sigmaMinus sigmaPlus f0 coefficient lambda -
      (1 / Real.pi) *
        (∫ theta in 0..Real.pi,
          platformAngularAdjointDensity
              a xMinus xPlus sigmaMinus sigmaPlus theta *
            platformAbelHilbertSeries (platformRadius a)
              coefficient lambda theta) =
      -endpointAdjointGamma (platformRadius a)
          sigmaMinus sigmaPlus (platformRho a xMinus)
            (platformRho a xPlus) *
        platformAbelEndpointSeriesValue f0 coefficient lambda := by
  let Gamma : ℝ := endpointAdjointGamma (platformRadius a)
    sigmaMinus sigmaPlus (platformRho a xMinus) (platformRho a xPlus)
  have hExterior := tendsto_platformAbelFiniteExteriorVariation
    (sigmaMinus := sigmaMinus) (sigmaPlus := sigmaPlus)
    hxMinus hxPlus ha2 hlambda hbound f0
  have hPairing :=
    tendsto_one_div_pi_mul_integral_platformDensity_finiteAbelTransform
      (sigmaMinus := sigmaMinus) (sigmaPlus := sigmaPlus)
      hxMinus hxPlus ha2 hlambda hbound
  have hEndpoint := tendsto_platformAbelFiniteCosinePolynomial_at_pi
    hlambda hbound f0
  have hLeft := hExterior.sub hPairing
  have hGamma : Tendsto (fun _N : ℕ ↦ -Gamma) atTop (nhds (-Gamma)) :=
    tendsto_const_nhds
  have hRight := hGamma.mul hEndpoint
  have hsequence :
      (fun N ↦
        platformAbelFiniteExteriorVariation a xMinus xPlus
            sigmaMinus sigmaPlus f0 coefficient lambda N -
          (1 / Real.pi) *
            (∫ theta in 0..Real.pi,
              platformAngularAdjointDensity
                  a xMinus xPlus sigmaMinus sigmaPlus theta *
                platformAbelFiniteHilbertTransform (platformRadius a)
                  coefficient lambda N theta)) =
      fun N ↦ -Gamma *
        platformAbelFiniteCosinePolynomial
          f0 coefficient lambda N Real.pi := by
    funext N
    simpa only [Gamma] using!
      platformAbelFiniteExteriorVariation_sub_adjointPairing
        hxMinus hxPlus ha2 f0 coefficient lambda N
  rw [hsequence] at hLeft
  have hlimit :
      platformAbelExteriorVariation a xMinus xPlus
          sigmaMinus sigmaPlus f0 coefficient lambda -
        platformAbelAdjointPairingSeries (platformRadius a)
          sigmaMinus sigmaPlus (platformRho a xMinus)
            (platformRho a xPlus) coefficient lambda =
        -Gamma * platformAbelEndpointSeriesValue
          f0 coefficient lambda :=
    tendsto_nhds_unique hLeft hRight
  rw [one_div_pi_mul_integral_platformAdjointDensity_mul_abelHilbertSeries
    hxMinus hxPlus ha2 hlambda hbound]
  simpa only [Gamma] using! hlimit

end

end Erdos1038
