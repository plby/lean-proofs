import ErdosProblems.Erdos1038.PlatformResidualMaterialExteriorIdentity
import ErdosProblems.Erdos1038.PlatformResidualLogTangentIntegrability

/-!
# Canonical Abel pairing limit for the residual material field

The endpoint-corrected Abel identity makes the adjoint-weighted Hilbert
pairing limit a consequence of the exterior Poisson limit and the concrete
one-sided material value at `pi`.  This file records that specialization for
the actual residual material Fourier coefficients and the canonical radii
`n / (n + 1)`.
-/

set_option warningAsError false

open Filter MeasureTheory Set
open scoped Topology

namespace Erdos1038

noncomputable section

variable {ι : Type*} [Fintype ι] [LinearOrder ι]

/-- The concrete analytic certificate left by the finite-jump argument in
the manuscript.  It records a single integrable majorant for the canonical
Abel Hilbert pairings and almost-everywhere convergence to the assembled
reduced directional field. -/
def PlatformResidualMaterialFiniteJumpPairingCertificate
    (C : ResidualConfiguration ι)
    (k a xMinus xPlus sigmaMinus sigmaPlus : ℝ)
    (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a) : Prop :=
  ∃ bound : ℝ → ℝ,
    IntervalIntegrable bound volume 0 Real.pi ∧
    (∀ n, AEStronglyMeasurable
      (fun theta : ℝ ↦
        platformAngularAdjointDensity
            a xMinus xPlus sigmaMinus sigmaPlus theta *
          platformAbelHilbertSeries (platformRadius a)
            (platformResidualMaterialCosineCoefficient
              C k a hk ha ha2 hthreshold)
            (canonicalAbelParameter n) theta)
      (volume.restrict (uIoc (0 : ℝ) Real.pi))) ∧
    (∀ n, ∀ᵐ theta ∂volume, theta ∈ uIoc (0 : ℝ) Real.pi →
      ‖platformAngularAdjointDensity
            a xMinus xPlus sigmaMinus sigmaPlus theta *
          platformAbelHilbertSeries (platformRadius a)
            (platformResidualMaterialCosineCoefficient
              C k a hk ha ha2 hthreshold)
            (canonicalAbelParameter n) theta‖ ≤ bound theta) ∧
    (∀ᵐ theta ∂volume, theta ∈ uIoc (0 : ℝ) Real.pi →
      Tendsto
        (fun n ↦
          platformAngularAdjointDensity
              a xMinus xPlus sigmaMinus sigmaPlus theta *
            platformAbelHilbertSeries (platformRadius a)
              (platformResidualMaterialCosineCoefficient
                C k a hk ha ha2 hthreshold)
              (canonicalAbelParameter n) theta)
        atTop
        (nhds
          (platformAngularAdjointDensity
              a xMinus xPlus sigmaMinus sigmaPlus theta *
            platformResidualPiecewiseReducedDirectionalField C k a
              hk ha ha2 hthreshold theta)))

/-- Every canonical Abel pairing integrand is measurable.  Thus the
measurability component of the finite-jump certificate is automatic; only
the uniform logarithmic majorant and its pointwise boundary limit carry
analytic content. -/
theorem aestronglyMeasurable_platformResidualMaterialAbelHilbertPairing_canonical
    (C : ResidualConfiguration ι)
    (k a xMinus xPlus sigmaMinus sigmaPlus : ℝ)
    (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a) (n : ℕ) :
    AEStronglyMeasurable
      (fun theta : ℝ ↦
        platformAngularAdjointDensity
            a xMinus xPlus sigmaMinus sigmaPlus theta *
          platformAbelHilbertSeries (platformRadius a)
            (platformResidualMaterialCosineCoefficient
              C k a hk ha ha2 hthreshold)
            (canonicalAbelParameter n) theta)
      (volume.restrict (uIoc (0 : ℝ) Real.pi)) := by
  have hB : Measurable (platformAngularAdjointDensity
      a xMinus xPlus sigmaMinus sigmaPlus) := by
    unfold platformAngularAdjointDensity adjointNumerator
      adjointNormalization platformCrossingScale platformAngularDistance
      platformCenter platformRadius
    fun_prop
  have hseries : Continuous
      (platformAbelHilbertSeries (platformRadius a)
        (platformResidualMaterialCosineCoefficient
          C k a hk ha ha2 hthreshold)
        (canonicalAbelParameter n)) :=
    continuous_platformAbelHilbertSeries
      (canonicalAbelParameter_isInteriorApproach.1 n)
      (platformResidualMaterialCosineCoefficient_bounded
        C k a hk ha ha2 hthreshold)
      (platformRadius a)
  exact (hB.mul hseries.measurable).aestronglyMeasurable

/-- The majorant and pointwise convergence in the finite-jump certificate
already imply integrability of the clean reduced-field pairing integrand. -/
theorem intervalIntegrable_platformResidualReducedDirectionalPairingIntegrand_of_certificate
    (C : ResidualConfiguration ι)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    {xMinus xPlus sigmaMinus sigmaPlus : ℝ}
    (hcertificate : PlatformResidualMaterialFiniteJumpPairingCertificate
      C k a xMinus xPlus sigmaMinus sigmaPlus hk ha ha2 hthreshold) :
    IntervalIntegrable
      (fun theta : ℝ ↦
        platformAngularAdjointDensity
            a xMinus xPlus sigmaMinus sigmaPlus theta *
          platformResidualPiecewiseReducedDirectionalField C k a
            hk ha ha2 hthreshold theta)
      volume 0 Real.pi := by
  rcases hcertificate with ⟨bound, hboundIntegrable, _hmeasurable,
    hbound, hpointwise⟩
  let target : ℝ → ℝ := fun theta ↦
    platformAngularAdjointDensity
        a xMinus xPlus sigmaMinus sigmaPlus theta *
      platformResidualPiecewiseReducedDirectionalField C k a
        hk ha ha2 hthreshold theta
  have htargetMeasurable : Measurable target := by
    dsimp only [target]
    apply Measurable.mul
    · unfold platformAngularAdjointDensity adjointNumerator
        adjointNormalization platformCrossingScale platformAngularDistance
        platformCenter platformRadius
      fun_prop
    · exact measurable_platformResidualPiecewiseReducedDirectionalField
        C k a hk ha ha2 hthreshold
  have hboundAll : ∀ᵐ theta ∂volume,
      ∀ n, theta ∈ uIoc (0 : ℝ) Real.pi →
        ‖platformAngularAdjointDensity
              a xMinus xPlus sigmaMinus sigmaPlus theta *
            platformAbelHilbertSeries (platformRadius a)
              (platformResidualMaterialCosineCoefficient
                C k a hk ha ha2 hthreshold)
              (canonicalAbelParameter n) theta‖ ≤ bound theta :=
    ae_all_iff.2 hbound
  have htargetBound : ∀ᵐ theta ∂volume,
      theta ∈ uIoc (0 : ℝ) Real.pi → ‖target theta‖ ≤ bound theta := by
    filter_upwards [hpointwise, hboundAll] with theta hlimit hle
    intro htheta
    exact le_of_tendsto
      (tendsto_norm.comp (hlimit htheta))
      (Eventually.of_forall fun n ↦ hle n htheta)
  have htargetBoundRestrict :
      (fun theta ↦ ‖target theta‖) ≤ᵐ[
        volume.restrict (uIoc (0 : ℝ) Real.pi)] bound := by
    filter_upwards [ae_restrict_mem measurableSet_uIoc,
      ae_restrict_of_ae htargetBound] with theta htheta hle
    exact hle htheta
  exact hboundIntegrable.mono_fun'
    htargetMeasurable.aestronglyMeasurable htargetBoundRestrict

/-- Packaging lemma for Dalton's exact block interface.  The difficult
upper-field integrability is supplied automatically by the same finite-jump
majorant used for Abel convergence; the remaining lower logarithmic block
integrals are independent static energy terms. -/
theorem platformResidualPairingIntegrable_of_lower_and_finiteJumpCertificate
    (C : ResidualConfiguration ι)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    {xMinus xPlus sigmaMinus sigmaPlus : ℝ}
    (hlower : ∀ i, IntervalIntegrable
      (fun theta : ℝ ↦
        platformAngularAdjointDensity
            a xMinus xPlus sigmaMinus sigmaPlus theta *
          platformResidualBlockLogTangentLower C k a
            hk ha ha2 hthreshold i theta)
      volume
      (platformResidualBlockLeft C k a hk ha ha2 hthreshold i)
      (platformResidualBlockRight C k a hk ha ha2 hthreshold i))
    (hcertificate : PlatformResidualMaterialFiniteJumpPairingCertificate
      C k a xMinus xPlus sigmaMinus sigmaPlus hk ha ha2 hthreshold) :
    PlatformResidualPairingIntegrable C k a
      xMinus xPlus sigmaMinus sigmaPlus hk ha ha2 hthreshold := by
  exact ⟨hlower,
    intervalIntegrable_platformResidualReducedDirectionalPairingIntegrand_of_certificate
      C k a hk ha ha2 hthreshold hcertificate⟩

/-- The concrete finite-jump certificate now discharges Dalton's complete
pairing-integrability interface: its majorant handles the upper reduced
field, while the static mixed-log estimate handles every lower block. -/
theorem platformResidualPairingIntegrable_of_finiteJumpCertificate
    (C : ResidualConfiguration ι)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    {xMinus xPlus sigmaMinus sigmaPlus : ℝ}
    (hxMinus : xMinus < a) (hxPlus : xPlus < a)
    (hsigmaMinus : 0 < sigmaMinus) (hsigmaPlus : 0 < sigmaPlus)
    (hcertificate : PlatformResidualMaterialFiniteJumpPairingCertificate
      C k a xMinus xPlus sigmaMinus sigmaPlus hk ha ha2 hthreshold) :
    PlatformResidualPairingIntegrable C k a
      xMinus xPlus sigmaMinus sigmaPlus hk ha ha2 hthreshold := by
  apply platformResidualPairingIntegrable_of_lower_and_finiteJumpCertificate
    C k a hk ha ha2 hthreshold
  · intro i
    exact intervalIntegrable_platformResidualBlockLogTangentPairingIntegrand
      C hk ha ha2 hthreshold hxMinus hxPlus
        hsigmaMinus hsigmaPlus i
  · exact hcertificate

/-- The canonical adjoint-weighted Abel Hilbert pairing of the residual
material field converges to its exterior boundary value plus the exact top
endpoint correction. -/
theorem tendsto_platformResidualMaterialAbelHilbertPairing_canonical
    (C : ResidualConfiguration ι)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    {xMinus xPlus sigmaMinus sigmaPlus : ℝ}
    (hxMinus : xMinus < a) (hxPlus : xPlus < a) :
    Tendsto
      (fun n ↦ (1 / Real.pi) *
        (∫ theta in 0..Real.pi,
          platformAngularAdjointDensity
              a xMinus xPlus sigmaMinus sigmaPlus theta *
            platformAbelHilbertSeries (platformRadius a)
              (platformResidualMaterialCosineCoefficient
                C k a hk ha ha2 hthreshold)
              (canonicalAbelParameter n) theta))
      atTop
      (nhds
        (platformBoundaryExteriorVariation a xMinus xPlus
            sigmaMinus sigmaPlus
            (platformResidualMaterialMean C k a hk ha ha2 hthreshold)
            (platformResidualMaterialCosineCoefficient
              C k a hk ha ha2 hthreshold) +
          endpointAdjointGamma (platformRadius a)
              sigmaMinus sigmaPlus (platformRho a xMinus)
                (platformRho a xPlus) *
            platformResidualMaterialField C k a hk ha ha2
              hthreshold Real.pi)) := by
  exact tendsto_platformAdjointPairing_of_exterior_endpoint_abel_limits
    hxMinus hxPlus ha2
    (platformResidualMaterialCosineCoefficient_bounded
      C k a hk ha ha2 hthreshold)
    (platformResidualMaterialMean C k a hk ha ha2 hthreshold)
    canonicalAbelParameter_isInteriorApproach
    (tendsto_platformAbelExteriorVariation_boundary
      hxMinus hxPlus ha2
      (platformResidualMaterialCosineCoefficient_bounded
        C k a hk ha ha2 hthreshold)
      (platformResidualMaterialMean C k a hk ha ha2 hthreshold)
      canonicalAbelParameter_isInteriorApproach)
    (tendsto_platformResidualMaterialAbelEndpoint_canonical
      C k a hk ha ha2 hthreshold)

/-- The finite-jump certificate gives convergence directly to the clean
block-side reduced-field pairing. -/
theorem tendsto_platformResidualMaterialAbelHilbertPairing_canonical_to_reducedPairing
    (C : ResidualConfiguration ι)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    {xMinus xPlus sigmaMinus sigmaPlus : ℝ}
    (hcertificate : PlatformResidualMaterialFiniteJumpPairingCertificate
      C k a xMinus xPlus sigmaMinus sigmaPlus hk ha ha2 hthreshold) :
    Tendsto
      (fun n ↦ (1 / Real.pi) *
        (∫ theta in 0..Real.pi,
          platformAngularAdjointDensity
              a xMinus xPlus sigmaMinus sigmaPlus theta *
            platformAbelHilbertSeries (platformRadius a)
              (platformResidualMaterialCosineCoefficient
                C k a hk ha ha2 hthreshold)
              (canonicalAbelParameter n) theta))
      atTop
      (nhds (platformResidualReducedDirectionalPairing C k a
        xMinus xPlus sigmaMinus sigmaPlus hk ha ha2 hthreshold)) := by
  rcases hcertificate with ⟨bound, hboundIntegrable, hmeasurable,
    hbound, hpointwise⟩
  have hintegral :=
    intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (F := fun n theta ↦
        platformAngularAdjointDensity
            a xMinus xPlus sigmaMinus sigmaPlus theta *
          platformAbelHilbertSeries (platformRadius a)
            (platformResidualMaterialCosineCoefficient
              C k a hk ha ha2 hthreshold)
            (canonicalAbelParameter n) theta)
      (f := fun theta ↦
        platformAngularAdjointDensity
            a xMinus xPlus sigmaMinus sigmaPlus theta *
          platformResidualPiecewiseReducedDirectionalField C k a
            hk ha ha2 hthreshold theta)
      bound (Eventually.of_forall hmeasurable)
      (Eventually.of_forall hbound) hboundIntegrable hpointwise
  have hscale := (tendsto_const_nhds.mul hintegral :
    Tendsto
      (fun n ↦ (1 / Real.pi) *
        (∫ theta in 0..Real.pi,
          platformAngularAdjointDensity
              a xMinus xPlus sigmaMinus sigmaPlus theta *
            platformAbelHilbertSeries (platformRadius a)
              (platformResidualMaterialCosineCoefficient
                C k a hk ha ha2 hthreshold)
              (canonicalAbelParameter n) theta))
      atTop
      (nhds ((1 / Real.pi) *
        (∫ theta in 0..Real.pi,
          platformAngularAdjointDensity
              a xMinus xPlus sigmaMinus sigmaPlus theta *
            platformResidualPiecewiseReducedDirectionalField C k a
              hk ha ha2 hthreshold theta))))
  simpa only [platformResidualReducedDirectionalPairing] using! hscale

/-- Exact finite-jump weak Hilbert identity for the concrete material
field, reduced to the explicit logarithmic-majorant certificate. -/
theorem platformResidualReducedDirectionalPairing_eq_boundaryExterior_add_endpoint
    (C : ResidualConfiguration ι)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    {xMinus xPlus sigmaMinus sigmaPlus : ℝ}
    (hxMinus : xMinus < a) (hxPlus : xPlus < a)
    (hcertificate : PlatformResidualMaterialFiniteJumpPairingCertificate
      C k a xMinus xPlus sigmaMinus sigmaPlus hk ha ha2 hthreshold) :
    platformResidualReducedDirectionalPairing C k a
        xMinus xPlus sigmaMinus sigmaPlus hk ha ha2 hthreshold =
      platformBoundaryExteriorVariation a xMinus xPlus
          sigmaMinus sigmaPlus
          (platformResidualMaterialMean C k a hk ha ha2 hthreshold)
          (platformResidualMaterialCosineCoefficient
            C k a hk ha ha2 hthreshold) +
        endpointAdjointGamma (platformRadius a)
            sigmaMinus sigmaPlus (platformRho a xMinus)
              (platformRho a xPlus) *
          platformResidualMaterialField C k a hk ha ha2
            hthreshold Real.pi := by
  exact tendsto_nhds_unique
    (tendsto_platformResidualMaterialAbelHilbertPairing_canonical_to_reducedPairing
      C k a hk ha ha2 hthreshold hcertificate)
    (tendsto_platformResidualMaterialAbelHilbertPairing_canonical
      C k a hk ha ha2 hthreshold hxMinus hxPlus)

/-- Once the finite-jump weak Hilbert identity identifies the clean reduced
field pairing with the forced exterior-plus-endpoint scalar, the canonical
Abel convergence has exactly the block-side target. -/
theorem tendsto_platformResidualMaterialAbelHilbertPairing_canonical_of_weakIdentity
    (C : ResidualConfiguration ι)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    {xMinus xPlus sigmaMinus sigmaPlus : ℝ}
    (hxMinus : xMinus < a) (hxPlus : xPlus < a)
    (hweak :
      platformResidualReducedDirectionalPairing C k a
          xMinus xPlus sigmaMinus sigmaPlus hk ha ha2 hthreshold =
        platformBoundaryExteriorVariation a xMinus xPlus
            sigmaMinus sigmaPlus
            (platformResidualMaterialMean C k a hk ha ha2 hthreshold)
            (platformResidualMaterialCosineCoefficient
              C k a hk ha ha2 hthreshold) +
          endpointAdjointGamma (platformRadius a)
              sigmaMinus sigmaPlus (platformRho a xMinus)
                (platformRho a xPlus) *
            platformResidualMaterialField C k a hk ha ha2
              hthreshold Real.pi) :
    Tendsto
      (fun n ↦ (1 / Real.pi) *
        (∫ theta in 0..Real.pi,
          platformAngularAdjointDensity
              a xMinus xPlus sigmaMinus sigmaPlus theta *
            platformAbelHilbertSeries (platformRadius a)
              (platformResidualMaterialCosineCoefficient
                C k a hk ha ha2 hthreshold)
              (canonicalAbelParameter n) theta))
      atTop
      (nhds (platformResidualReducedDirectionalPairing C k a
        xMinus xPlus sigmaMinus sigmaPlus hk ha ha2 hthreshold)) := by
  rw [hweak]
  exact tendsto_platformResidualMaterialAbelHilbertPairing_canonical
    C k a hk ha ha2 hthreshold hxMinus hxPlus

end

end Erdos1038
