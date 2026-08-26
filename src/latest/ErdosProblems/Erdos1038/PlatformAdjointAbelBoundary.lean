import ErdosProblems.Erdos1038.PlatformAdjointAbelIdentity

/-!
# Passing the endpoint-corrected Abel identity to the boundary

The analytic work for an atomic material velocity naturally produces three
separate limits as an interior Abel parameter tends to one: the exterior
variation, the adjoint pairing, and the endpoint value.  This file isolates
the exact limit passage.  In particular, once the endpoint limit is
nonpositive, the endpoint correction has the sign needed by the platform
supporting argument.
-/

set_option warningAsError false

open Filter MeasureTheory Set
open scoped Topology

namespace Erdos1038

noncomputable section

/-- A sequence approaches the Abel boundary from inside the open unit
interval.  The convergence component records the intended boundary regime;
the pointwise component is what licenses every interior identity. -/
def InteriorAbelApproach (lambda : ℕ → ℝ) : Prop :=
  (∀ n, |lambda n| < 1) ∧ Tendsto lambda atTop (nhds 1)

/-- A canonical explicit approach to the Abel boundary. -/
def canonicalAbelParameter (n : ℕ) : ℝ :=
  n / (n + 1)

theorem canonicalAbelParameter_isInteriorApproach :
    InteriorAbelApproach canonicalAbelParameter := by
  constructor
  · intro n
    have hn : 0 ≤ (n : ℝ) := by positivity
    have hden : 0 < (n : ℝ) + 1 := by positivity
    rw [canonicalAbelParameter, abs_of_nonneg (div_nonneg hn hden.le)]
    exact (div_lt_one hden).2 (by linarith)
  · simpa only [canonicalAbelParameter, Nat.cast_add, Nat.cast_one] using!
      (tendsto_natCast_div_add_atTop (1 : ℝ))

/-- The fixed-parameter endpoint-corrected identity survives any interior
Abel approach for which its three constituent expressions have limits. -/
theorem platformAdjoint_boundary_identity_of_abel_limits
    {a xMinus xPlus sigmaMinus sigmaPlus : ℝ}
    (hxMinus : xMinus < a) (hxPlus : xPlus < a) (ha2 : a < 2)
    {coefficient : ℕ → ℝ} {C : ℝ}
    (hbound : RealSequenceBoundedBy coefficient C)
    (f0 : ℝ) {lambda : ℕ → ℝ}
    (hlambda : InteriorAbelApproach lambda)
    {exteriorLimit pairingLimit endpointLimit : ℝ}
    (hExterior : Tendsto
      (fun n ↦ platformAbelExteriorVariation a xMinus xPlus
        sigmaMinus sigmaPlus f0 coefficient (lambda n))
      atTop (nhds exteriorLimit))
    (hPairing : Tendsto
      (fun n ↦ (1 / Real.pi) *
        (∫ theta in 0..Real.pi,
          platformAngularAdjointDensity
              a xMinus xPlus sigmaMinus sigmaPlus theta *
            platformAbelHilbertSeries (platformRadius a)
              coefficient (lambda n) theta))
      atTop (nhds pairingLimit))
    (hEndpoint : Tendsto
      (fun n ↦ platformAbelEndpointSeriesValue
        f0 coefficient (lambda n))
      atTop (nhds endpointLimit)) :
    exteriorLimit - pairingLimit =
      -endpointAdjointGamma (platformRadius a)
          sigmaMinus sigmaPlus (platformRho a xMinus)
            (platformRho a xPlus) * endpointLimit := by
  let Gamma : ℝ := endpointAdjointGamma (platformRadius a)
    sigmaMinus sigmaPlus (platformRho a xMinus) (platformRho a xPlus)
  have hLeft := hExterior.sub hPairing
  have hGamma : Tendsto (fun _n : ℕ ↦ -Gamma) atTop (nhds (-Gamma)) :=
    tendsto_const_nhds
  have hRight := hGamma.mul hEndpoint
  have hPointwise : ∀ n,
      platformAbelExteriorVariation a xMinus xPlus
          sigmaMinus sigmaPlus f0 coefficient (lambda n) -
        (1 / Real.pi) *
          (∫ theta in 0..Real.pi,
            platformAngularAdjointDensity
                a xMinus xPlus sigmaMinus sigmaPlus theta *
              platformAbelHilbertSeries (platformRadius a)
                coefficient (lambda n) theta) =
        -Gamma * platformAbelEndpointSeriesValue
          f0 coefficient (lambda n) := by
    intro n
    simpa only [Gamma] using!
      platformAbelExteriorVariation_sub_platformAdjointPairing
        hxMinus hxPlus ha2 (hlambda.1 n) hbound f0
  have hLeftOnRight : Tendsto
      (fun n ↦ -Gamma * platformAbelEndpointSeriesValue
        f0 coefficient (lambda n))
      atTop (nhds (exteriorLimit - pairingLimit)) :=
    hLeft.congr' (Eventually.of_forall hPointwise)
  have hlimit : exteriorLimit - pairingLimit = -Gamma * endpointLimit :=
    tendsto_nhds_unique hLeftOnRight hRight
  simpa only [Gamma] using! hlimit

theorem endpointAdjointGamma_nonneg_of_nonneg
    {a xMinus xPlus sigmaMinus sigmaPlus : ℝ}
    (hxMinus : xMinus < a) (hxPlus : xPlus < a) (ha2 : a < 2)
    (hsigmaMinus : 0 ≤ sigmaMinus) (hsigmaPlus : 0 ≤ sigmaPlus) :
    0 ≤ endpointAdjointGamma (platformRadius a)
      sigmaMinus sigmaPlus (platformRho a xMinus)
        (platformRho a xPlus) := by
  rw [endpointAdjointGamma_eq_crossingScales hxMinus hxPlus ha2]
  exact add_nonneg
    (div_nonneg hsigmaMinus (platformCrossingScale_pos hxMinus ha2).le)
    (div_nonneg hsigmaPlus (platformCrossingScale_pos hxPlus ha2).le)

/-- The adjoint pairing has no independent boundary-limit content.  The
fixed-parameter endpoint-corrected identity expresses it pointwise as the
sum of the exterior variation and the endpoint correction, so convergence
of those two terms forces convergence of the pairing. -/
theorem tendsto_platformAdjointPairing_of_exterior_endpoint_abel_limits
    {a xMinus xPlus sigmaMinus sigmaPlus : ℝ}
    (hxMinus : xMinus < a) (hxPlus : xPlus < a) (ha2 : a < 2)
    {coefficient : ℕ → ℝ} {C : ℝ}
    (hbound : RealSequenceBoundedBy coefficient C)
    (f0 : ℝ) {lambda : ℕ → ℝ}
    (hlambda : InteriorAbelApproach lambda)
    {exteriorLimit endpointLimit : ℝ}
    (hExterior : Tendsto
      (fun n ↦ platformAbelExteriorVariation a xMinus xPlus
        sigmaMinus sigmaPlus f0 coefficient (lambda n))
      atTop (nhds exteriorLimit))
    (hEndpoint : Tendsto
      (fun n ↦ platformAbelEndpointSeriesValue
        f0 coefficient (lambda n))
      atTop (nhds endpointLimit)) :
    Tendsto
      (fun n ↦ (1 / Real.pi) *
        (∫ theta in 0..Real.pi,
          platformAngularAdjointDensity
              a xMinus xPlus sigmaMinus sigmaPlus theta *
            platformAbelHilbertSeries (platformRadius a)
              coefficient (lambda n) theta))
      atTop
      (nhds (exteriorLimit +
        endpointAdjointGamma (platformRadius a)
          sigmaMinus sigmaPlus (platformRho a xMinus)
            (platformRho a xPlus) * endpointLimit)) := by
  let Gamma := endpointAdjointGamma (platformRadius a)
    sigmaMinus sigmaPlus (platformRho a xMinus) (platformRho a xPlus)
  have hGamma : Tendsto (fun _n : ℕ ↦ Gamma) atTop (nhds Gamma) :=
    tendsto_const_nhds
  have hsum := hExterior.add (hGamma.mul hEndpoint)
  apply hsum.congr'
  filter_upwards with n
  have hid :=
    platformAbelExteriorVariation_sub_platformAdjointPairing
      (sigmaMinus := sigmaMinus) (sigmaPlus := sigmaPlus)
      hxMinus hxPlus ha2 (hlambda.1 n) hbound f0
  dsimp only [Gamma]
  linarith

/-- Consequently the endpoint sign alone makes the forced pairing limit no
larger than the exterior limit. -/
theorem platformAdjointPairingLimit_le_exterior_of_endpoint_nonpos
    {a xMinus xPlus sigmaMinus sigmaPlus exteriorLimit endpointLimit : ℝ}
    (hxMinus : xMinus < a) (hxPlus : xPlus < a) (ha2 : a < 2)
    (hsigmaMinus : 0 ≤ sigmaMinus) (hsigmaPlus : 0 ≤ sigmaPlus)
    (hEndpointNonpos : endpointLimit ≤ 0) :
    exteriorLimit +
        endpointAdjointGamma (platformRadius a)
          sigmaMinus sigmaPlus (platformRho a xMinus)
            (platformRho a xPlus) * endpointLimit ≤
      exteriorLimit := by
  have hGamma := endpointAdjointGamma_nonneg_of_nonneg
    hxMinus hxPlus ha2 hsigmaMinus hsigmaPlus
  exact add_le_of_nonpos_right (mul_nonpos_of_nonneg_of_nonpos
    hGamma hEndpointNonpos)

/-- Sign form used by the endpoint-corrected supporting inequality: a
nonpositive top velocity makes the unregularized adjoint pairing no larger
than the exterior/material directional variation. -/
theorem platformAdjointPairing_le_exterior_of_abel_limits
    {a xMinus xPlus sigmaMinus sigmaPlus : ℝ}
    (hxMinus : xMinus < a) (hxPlus : xPlus < a) (ha2 : a < 2)
    (hsigmaMinus : 0 ≤ sigmaMinus) (hsigmaPlus : 0 ≤ sigmaPlus)
    {coefficient : ℕ → ℝ} {C : ℝ}
    (hbound : RealSequenceBoundedBy coefficient C)
    (f0 : ℝ) {lambda : ℕ → ℝ}
    (hlambda : InteriorAbelApproach lambda)
    {exteriorLimit pairingLimit endpointLimit : ℝ}
    (hExterior : Tendsto
      (fun n ↦ platformAbelExteriorVariation a xMinus xPlus
        sigmaMinus sigmaPlus f0 coefficient (lambda n))
      atTop (nhds exteriorLimit))
    (hPairing : Tendsto
      (fun n ↦ (1 / Real.pi) *
        (∫ theta in 0..Real.pi,
          platformAngularAdjointDensity
              a xMinus xPlus sigmaMinus sigmaPlus theta *
            platformAbelHilbertSeries (platformRadius a)
              coefficient (lambda n) theta))
      atTop (nhds pairingLimit))
    (hEndpoint : Tendsto
      (fun n ↦ platformAbelEndpointSeriesValue
        f0 coefficient (lambda n))
      atTop (nhds endpointLimit))
    (hEndpointNonpos : endpointLimit ≤ 0) :
    pairingLimit ≤ exteriorLimit := by
  have hidentity := platformAdjoint_boundary_identity_of_abel_limits
    hxMinus hxPlus ha2 hbound f0 hlambda hExterior hPairing hEndpoint
  have hGamma := endpointAdjointGamma_nonneg_of_nonneg
    hxMinus hxPlus ha2 hsigmaMinus hsigmaPlus
  have hproduct : 0 ≤
      endpointAdjointGamma (platformRadius a)
          sigmaMinus sigmaPlus (platformRho a xMinus)
            (platformRho a xPlus) * (-endpointLimit) :=
    mul_nonneg hGamma (neg_nonneg.mpr hEndpointNonpos)
  nlinarith

end

end Erdos1038
