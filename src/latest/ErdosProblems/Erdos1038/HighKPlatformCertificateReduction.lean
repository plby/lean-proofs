import ErdosProblems.Erdos1038.NormalizedResidualPlatformCanonicalFiniteJump
import ErdosProblems.Erdos1038.HighKFunctionalBridge
import ErdosProblems.Erdos1038.FinalOneCutAssembly
import ErdosProblems.Erdos1038.PlatformResidualMaterialFiniteJumpCertificate

/-!
# Final reduction to the concrete high-k platform certificate

All non-high-ratio clauses of `MainTheorem` are already unconditional.  The
certificate below records exactly what the completed affine, constant, and
terminal cover must supply at each normalized residual ratio: one genuine
platform, its explicit simple crossings, one certified scalar regime, and
the canonical finite-jump dominated-convergence fact.
-/

set_option warningAsError false

open Polynomial

namespace Erdos1038

noncomputable section

/-- The single concrete certificate remaining after the canonical support,
block tangent, scalar calibration, and normalization assemblies. -/
def HighKNormalizedPlatformCertificate : Prop :=
  ∀ (g : Polynomial ℝ) (h : EndpointNormalizationHypotheses g),
    ∀ hres : endpointResidualRoots h.normalizedPolynomial ≠ 0,
      29 / 20 < normalizedEndpointResidualRatio h →
        ∃ (platformA xMinus xPlus : ℝ)
          (hk : 1 ≤ normalizedEndpointResidualRatio h)
          (ha : 0 < platformA) (_ha1 : 1 ≤ platformA)
          (ha2 : platformA < 2)
          (hthreshold : platformThreshold
            (normalizedEndpointResidualRatio h) ≤ platformA),
          PlatformExplicitExteriorCrossingCertificate
              (normalizedEndpointResidualRatio h) platformA
              xMinus xPlus ∧
            PlatformEffectiveCalibration
              (normalizedEndpointResidualRatio h) platformA
              xMinus xPlus
              (-1 / platformExteriorWx (normalizedEndpointResidualRatio h)
                platformA xMinus)
              (1 / platformExteriorWx (normalizedEndpointResidualRatio h)
                platformA xPlus) ∧
            PlatformResidualMaterialFiniteJumpPairingCertificate
              (h.normalizedResidualConfiguration hres)
              (normalizedEndpointResidualRatio h) platformA
              xMinus xPlus
              (platformReferenceNegativeCrossingAdjointWeight
                (h.normalizedResidualConfiguration hres)
                (normalizedEndpointResidualRatio h) platformA
                hk ha ha2 hthreshold xMinus)
              (platformReferencePositiveCrossingAdjointWeight
                (h.normalizedResidualConfiguration hres)
                (normalizedEndpointResidualRatio h) platformA
                hk ha ha2 hthreshold xPlus)
              hk ha ha2 hthreshold

/-- Purely explicit numerical/elementary part of the high-k certificate. -/
def HighKExplicitPlatformCalibrationCover : Prop :=
  ∀ k : ℝ, 29 / 20 < k →
    ∃ (platformA xMinus xPlus : ℝ)
      (_hk : 1 ≤ k) (_ha : 0 < platformA)
      (_ha1 : 1 ≤ platformA) (_ha2 : platformA < 2)
      (_hthreshold : platformThreshold k ≤ platformA),
      PlatformExplicitExteriorCrossingCertificate
          k platformA xMinus xPlus ∧
        PlatformEffectiveCalibration k platformA xMinus xPlus
          (-1 / platformExteriorWx k platformA xMinus)
          (1 / platformExteriorWx k platformA xPlus)

/-- Configuration-uniform analytic statement left by the finite-jump
argument.  Its geometric hypotheses are exactly those supplied by every
explicit crossing certificate. -/
def PlatformResidualMaterialUniformFiniteJumpCertificate : Prop :=
  ∀ {iota : Type} [Fintype iota] [LinearOrder iota]
    (C : ResidualConfiguration iota)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    (xMinus xPlus sigmaMinus sigmaPlus : ℝ)
    (_hxMinus : xMinus < a) (_hxPlus : xPlus < a)
    (_hsigmaMinus : 0 < sigmaMinus) (_hsigmaPlus : 0 < sigmaPlus),
    PlatformResidualMaterialFiniteJumpPairingCertificate
      C k a xMinus xPlus sigmaMinus sigmaPlus hk ha ha2 hthreshold

/-- The configuration-uniform finite-jump certificate follows from the
explicit boundary logarithmic majorant and canonical Abel convergence. -/
theorem platformResidualMaterialUniformFiniteJumpCertificate :
    PlatformResidualMaterialUniformFiniteJumpCertificate := by
  intro iota _instFintype _instLinearOrder C
    k a hk ha ha2 hthreshold
    xMinus xPlus sigmaMinus sigmaPlus
    hxMinus hxPlus hsigmaMinus hsigmaPlus
  exact platformResidualMaterialFiniteJumpPairingCertificate
    C k a hk ha ha2 hthreshold
      xMinus xPlus sigmaMinus sigmaPlus
      hxMinus hxPlus hsigmaMinus hsigmaPlus

/-- The explicit parameter cover and the configuration-uniform finite-jump
theorem assemble into the one concrete certificate consumed below. -/
theorem highKNormalizedPlatformCertificate_of_cover_and_uniformFiniteJump
    (hcover : HighKExplicitPlatformCalibrationCover)
    (hfiniteJump : PlatformResidualMaterialUniformFiniteJumpCertificate) :
    HighKNormalizedPlatformCertificate := by
  intro g h hres hkHigh
  let k := normalizedEndpointResidualRatio h
  let C := h.normalizedResidualConfiguration hres
  rcases hcover k hkHigh with
    ⟨platformA, xMinus, xPlus, hk, ha, ha1, ha2, hthreshold,
      hcrossing, hcalibration⟩
  have hcanonical := hcrossing.toCanonical C hk ha ha2 hthreshold
  have hjump := hfiniteJump C k platformA hk ha ha2 hthreshold
    xMinus xPlus
    (platformReferenceNegativeCrossingAdjointWeight C k platformA
      hk ha ha2 hthreshold xMinus)
    (platformReferencePositiveCrossingAdjointWeight C k platformA
      hk ha ha2 hthreshold xPlus)
    (hcrossing.xMinus_neg.trans ha) hcrossing.xPlus_lt_platform
    hcanonical.negativeWeight_pos hcanonical.positiveWeight_pos
  exact ⟨platformA, xMinus, xPlus, hk, ha, ha1, ha2, hthreshold,
    hcrossing, hcalibration, hjump⟩

/-- The concrete platform certificate is exactly sufficient for the
normalized strict functional. -/
theorem highKNormalizedFunctional_of_platformCertificate
    (hcertificate : HighKNormalizedPlatformCertificate) :
    HighKNormalizedFunctionalStrictLowerBound := by
  intro g h hres hkHigh
  rcases hcertificate g h hres hkHigh with
    ⟨platformA, xMinus, xPlus, hk, ha, ha1, ha2, hthreshold,
      hcrossing, hcalibration, hfiniteJump⟩
  exact h.normalized_functional_strict_of_finiteJumpExplicitCrossing
    hres hk ha ha1 ha2 hthreshold hcrossing hcalibration hfiniteJump

/-- The completed concrete high-k platform certificate closes the exact
parameter-free theorem. -/
theorem mainTheorem_of_highKNormalizedPlatformCertificate
    (hcertificate : HighKNormalizedPlatformCertificate) : MainTheorem := by
  apply mainTheorem_of_highKEndpointStrictLowerBound
  apply highKEndpointStrictLowerBound_of_normalizedFunctional
  exact highKNormalizedFunctional_of_platformCertificate hcertificate

/-- Final parameter-free theorem from the two genuinely independent
remaining certificates. -/
theorem mainTheorem_of_explicitPlatformCover_and_uniformFiniteJump
    (hcover : HighKExplicitPlatformCalibrationCover)
    (hfiniteJump : PlatformResidualMaterialUniformFiniteJumpCertificate) :
    MainTheorem := by
  apply mainTheorem_of_highKNormalizedPlatformCertificate
  exact highKNormalizedPlatformCertificate_of_cover_and_uniformFiniteJump
    hcover hfiniteJump

/-- Once the explicit scalar platform cover is supplied, the finite-jump
analytic input is now discharged unconditionally. -/
theorem mainTheorem_of_explicitPlatformCover
    (hcover : HighKExplicitPlatformCalibrationCover) : MainTheorem :=
  mainTheorem_of_explicitPlatformCover_and_uniformFiniteJump
    hcover platformResidualMaterialUniformFiniteJumpCertificate

end

end Erdos1038
