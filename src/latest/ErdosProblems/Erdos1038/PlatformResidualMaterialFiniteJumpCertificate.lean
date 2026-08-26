import ErdosProblems.Erdos1038.PlatformResidualMaterialAbelPairingLimit
import ErdosProblems.Erdos1038.PlatformResidualMaterialBoundaryConvergence
import ErdosProblems.Erdos1038.PlatformResidualMaterialBoundaryIdentification
import ErdosProblems.Erdos1038.PlatformResidualMaterialBoundaryMajorant
import ErdosProblems.Erdos1038.PlatformResidualOpenBlockPartition

set_option warningAsError false

open Filter MeasureTheory Set
open scoped Topology

namespace Erdos1038

noncomputable section

variable {iota : Type*} [Fintype iota] [LinearOrder iota]

/-- At every non-endpoint point in an open residual block, the canonical
Abel Hilbert pairing converges to that block's reduced directional field. -/
theorem tendsto_platformResidualMaterialAbelHilbertPairing_pointwise
    (C : ResidualConfiguration iota)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    (xMinus xPlus sigmaMinus sigmaPlus : ℝ)
    {theta : ℝ} (i : iota)
    (htheta : theta ∈ Ioo
      (platformResidualBlockLeft C k a hk ha ha2 hthreshold i)
      (platformResidualBlockRight C k a hk ha ha2 hthreshold i))
    (hleftNe : ∀ j, theta ≠
      platformResidualBlockLeft C k a hk ha ha2 hthreshold j)
    (hrightNe : ∀ j, theta ≠
      platformResidualBlockRight C k a hk ha ha2 hthreshold j) :
    Tendsto
      (fun n ↦ platformAngularAdjointDensity
          a xMinus xPlus sigmaMinus sigmaPlus theta *
        platformAbelHilbertSeries (platformRadius a)
          (platformResidualMaterialCosineCoefficient
            C k a hk ha ha2 hthreshold)
          (canonicalAbelParameter n) theta)
      atTop
      (𝓝 (platformAngularAdjointDensity
          a xMinus xPlus sigmaMinus sigmaPlus theta *
        platformResidualPiecewiseReducedDirectionalField C k a
          hk ha ha2 hthreshold theta)) := by
  let B := platformAngularAdjointDensity
    a xMinus xPlus sigmaMinus sigmaPlus theta
  let scalar := -(2 / platformRadius a) * (1 / Real.pi)
  have hthetaHalf : theta ∈ Ioo (0 : ℝ) Real.pi :=
    ⟨(platformResidualBlockLeft_mem_Icc C k a hk ha ha2
        hthreshold i).1.trans_lt htheta.1,
      htheta.2.trans_le
        (platformResidualBlockRight_mem_Icc C k a hk ha ha2
          hthreshold i).2⟩
  have hsin : 0 < Real.sin theta :=
    Real.sin_pos_of_pos_of_lt_pi hthetaHalf.1 hthetaHalf.2
  have hrep :=
    tendsto_platformResidualMaterialAbelLogRepresentation_canonical
      C k a hk ha ha2 hthreshold hthetaHalf hleftNe hrightNe
  have hscaled : Tendsto
      (fun n ↦ scalar * (B / Real.sin theta) *
        platformResidualMaterialAbelLogRepresentation C k a
          hk ha ha2 hthreshold (canonicalAbelParameter n) theta)
      atTop
      (𝓝 (scalar * (B / Real.sin theta) *
        platformResidualMaterialBoundaryLogRepresentation C k a
          hk ha ha2 hthreshold theta)) := by
    simpa only [mul_assoc] using!
      (hrep.const_mul (B / Real.sin theta)).const_mul scalar
  have hpair (n : ℕ) :
      platformAngularAdjointDensity
          a xMinus xPlus sigmaMinus sigmaPlus theta *
        platformAbelHilbertSeries (platformRadius a)
          (platformResidualMaterialCosineCoefficient
            C k a hk ha ha2 hthreshold)
          (canonicalAbelParameter n) theta =
        scalar * (B / Real.sin theta) *
          platformResidualMaterialAbelLogRepresentation C k a
            hk ha ha2 hthreshold (canonicalAbelParameter n) theta := by
    have hconjugate :=
      platformResidualMaterialAbelHilbertSeries_mul_sin_eq_conjugatePoisson
        C k a hk ha ha2 hthreshold
          (canonicalAbelParameter_isInteriorApproach.1 n) theta
    rw [integral_platformResidualMaterial_mul_conjugatePoisson_eq_abelLogRepresentation
        C k a hk ha ha2 hthreshold
          (canonicalAbelParameter_isInteriorApproach.1 n) theta] at hconjugate
    dsimp only [scalar, B]
    calc
      platformAngularAdjointDensity
            a xMinus xPlus sigmaMinus sigmaPlus theta *
          platformAbelHilbertSeries (platformRadius a)
            (platformResidualMaterialCosineCoefficient
              C k a hk ha ha2 hthreshold)
            (canonicalAbelParameter n) theta =
        (platformAngularAdjointDensity
            a xMinus xPlus sigmaMinus sigmaPlus theta /
              Real.sin theta) *
          (platformAbelHilbertSeries (platformRadius a)
            (platformResidualMaterialCosineCoefficient
              C k a hk ha ha2 hthreshold)
            (canonicalAbelParameter n) theta * Real.sin theta) := by
              field_simp [hsin.ne']
      _ = _ := by rw [hconjugate]; ring
  have hidentification :=
    scaled_platformResidualMaterialBoundaryLogRepresentation_eq_reducedDirectionalField
      C k a hk ha ha2 hthreshold i htheta
  have hpiecewise :=
    platformResidualPiecewiseReducedDirectionalField_eq_on_block
      C k a hk ha ha2 hthreshold i
        (show theta ∈ Ioc
          (platformResidualBlockLeft C k a hk ha ha2 hthreshold i)
          (platformResidualBlockRight C k a hk ha ha2 hthreshold i) from
            ⟨htheta.1, htheta.2.le⟩)
  have htarget :
      scalar * (B / Real.sin theta) *
          platformResidualMaterialBoundaryLogRepresentation C k a
            hk ha ha2 hthreshold theta =
        platformAngularAdjointDensity
            a xMinus xPlus sigmaMinus sigmaPlus theta *
          platformResidualPiecewiseReducedDirectionalField C k a
            hk ha ha2 hthreshold theta := by
    rw [hpiecewise, ← hidentification]
    dsimp only [scalar, B]
    field_simp [hsin.ne']
  rw [← htarget]
  refine hscaled.congr' ?_
  exact Eventually.of_forall fun n ↦ (hpair n).symm

/-- The canonical Abel Hilbert pairing converges almost everywhere to the
assembled piecewise reduced directional field. -/
theorem ae_tendsto_platformResidualMaterialAbelHilbertPairing_canonical
    (C : ResidualConfiguration iota)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    (xMinus xPlus sigmaMinus sigmaPlus : ℝ) :
    ∀ᵐ theta ∂volume, theta ∈ uIoc (0 : ℝ) Real.pi →
      Tendsto
        (fun n ↦ platformAngularAdjointDensity
            a xMinus xPlus sigmaMinus sigmaPlus theta *
          platformAbelHilbertSeries (platformRadius a)
            (platformResidualMaterialCosineCoefficient
              C k a hk ha ha2 hthreshold)
            (canonicalAbelParameter n) theta)
        atTop
        (𝓝 (platformAngularAdjointDensity
            a xMinus xPlus sigmaMinus sigmaPlus theta *
          platformResidualPiecewiseReducedDirectionalField C k a
            hk ha ha2 hthreshold theta)) := by
  have hleftNe : ∀ᵐ theta ∂volume, ∀ i,
      theta ≠ platformResidualBlockLeft C k a hk ha ha2 hthreshold i :=
    ae_all_iff.2 (fun i ↦ Measure.ae_ne (volume : Measure ℝ)
      (platformResidualBlockLeft C k a hk ha ha2 hthreshold i))
  have hrightNe : ∀ᵐ theta ∂volume, ∀ i,
      theta ≠ platformResidualBlockRight C k a hk ha ha2 hthreshold i :=
    ae_all_iff.2 (fun i ↦ Measure.ae_ne (volume : Measure ℝ)
      (platformResidualBlockRight C k a hk ha ha2 hthreshold i))
  have hblock := ae_exists_mem_Ioo_platformResidualBlock
    C k a hk ha ha2 hthreshold
  filter_upwards [hleftNe, hrightNe, hblock]
    with theta hleft hright hcontains
  intro htheta
  rcases hcontains htheta with ⟨i, hi⟩
  exact tendsto_platformResidualMaterialAbelHilbertPairing_pointwise
    C k a hk ha ha2 hthreshold
    xMinus xPlus sigmaMinus sigmaPlus i hi hleft hright

/-- The finite-jump analytic certificate is unconditional under the natural
platform geometry and positive adjoint-weight assumptions. -/
theorem platformResidualMaterialFiniteJumpPairingCertificate
    (C : ResidualConfiguration iota)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    (xMinus xPlus sigmaMinus sigmaPlus : ℝ)
    (hxMinus : xMinus < a) (hxPlus : xPlus < a)
    (hsigmaMinus : 0 < sigmaMinus) (hsigmaPlus : 0 < sigmaPlus) :
    PlatformResidualMaterialFiniteJumpPairingCertificate C k a
      xMinus xPlus sigmaMinus sigmaPlus hk ha ha2 hthreshold := by
  let bound := platformResidualMaterialBoundaryPairingMajorant C k a
    hk ha ha2 hthreshold xMinus xPlus sigmaMinus sigmaPlus
  refine ⟨bound, ?_, ?_, ?_, ?_⟩
  · dsimp only [bound]
    exact intervalIntegrable_platformResidualMaterialBoundaryPairingMajorant
      C k a hk ha ha2 hthreshold
        xMinus xPlus sigmaMinus sigmaPlus
        hxMinus hxPlus hsigmaMinus hsigmaPlus
  · intro n
    exact
      aestronglyMeasurable_platformResidualMaterialAbelHilbertPairing_canonical
        C k a xMinus xPlus sigmaMinus sigmaPlus
          hk ha ha2 hthreshold n
  · intro n
    have hleftNe : ∀ᵐ theta ∂volume, ∀ i,
        theta ≠ platformResidualBlockLeft C k a hk ha ha2 hthreshold i :=
      ae_all_iff.2 (fun i ↦ Measure.ae_ne (volume : Measure ℝ)
        (platformResidualBlockLeft C k a hk ha ha2 hthreshold i))
    have hrightNe : ∀ᵐ theta ∂volume, ∀ i,
        theta ≠ platformResidualBlockRight C k a hk ha ha2 hthreshold i :=
      ae_all_iff.2 (fun i ↦ Measure.ae_ne (volume : Measure ℝ)
        (platformResidualBlockRight C k a hk ha ha2 hthreshold i))
    filter_upwards [hleftNe, hrightNe,
      Measure.ae_ne (volume : Measure ℝ) Real.pi]
      with theta hleft hright hpi
    intro htheta
    rw [uIoc_of_le Real.pi_pos.le] at htheta
    have hthetaIoo : theta ∈ Ioo (0 : ℝ) Real.pi :=
      ⟨htheta.1, lt_of_le_of_ne htheta.2 hpi⟩
    dsimp only [bound]
    exact
      norm_platformResidualMaterialAbelHilbertPairing_canonical_le_majorant
        C k a hk ha ha2 hthreshold
          xMinus xPlus sigmaMinus sigmaPlus
          hxMinus hxPlus hsigmaMinus hsigmaPlus
          hthetaIoo hleft hright n
  · exact ae_tendsto_platformResidualMaterialAbelHilbertPairing_canonical
      C k a hk ha ha2 hthreshold
        xMinus xPlus sigmaMinus sigmaPlus

end

end Erdos1038
