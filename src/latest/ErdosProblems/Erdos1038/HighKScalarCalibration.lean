import ErdosProblems.Erdos1038.PlatformCircleBlock
import ErdosProblems.Erdos1038.PlatformDeficitEnergy
import ErdosProblems.Erdos1038.CircleSelfFourier

/-!
# Exact scalar calibration for the high-ratio circle blocks

The numerical verifier does not need to certify the block margin separately
for every target interval.  This file proves the two rectangle reductions
used by the verifier:

* on a constant-edge slab, one endpoint scalar controls the whole rectangle;
* on an affine slab, a left scalar, a corner scalar, and the sign of one
  explicit derivative control the whole rectangle.

It also proves the exact full-mass caps for the concrete platform radii.  Thus
the remaining computer certificate concerns only the finitely many parameter
slabs and the displayed one-variable scalar, not arbitrary quantile blocks.
-/

set_option warningAsError false

open Set MeasureTheory
open scoped BigOperators

namespace Erdos1038

noncomputable section

/-- The parameter-independent part of the retained-square lower bound. -/
def circleRectangleBase
    (H aPi bPi Qmax Rmax : ℝ) : ℝ :=
  Real.log (2 * H / (aPi * bPi)) +
    circleCorrection Qmax + circleCorrection Rmax

/-- The favorable effective-platform coefficient `P` from the manuscript. -/
def circleEffectivePenalty (aPi Ceff : ℝ) : ℝ :=
  -Real.pi * Ceff / aPi

/-- The one-variable scalar retained on the affine part of the cover. -/
def affineCircleScalar
    (H aPi bPi Ceff Rmax Qmax Q : ℝ) : ℝ :=
  circleRectangleBase H aPi bPi Qmax Rmax +
    circleEffectivePenalty aPi Ceff / Q +
      (Real.sinc Q - Real.sinc Rmax) ^ 2

/-- Its explicit derivative, in the cancellation-free form checked on each
`Q` subcell of the numerical certificate. -/
def affineCircleScalarDerivative
    (aPi Ceff Rmax Q : ℝ) : ℝ :=
  -circleEffectivePenalty aPi Ceff / Q ^ 2 +
    2 * (Real.sinc Q - Real.sinc Rmax) *
      (-sincNumerator Q / Q ^ 2)

/-- The full square-completion gap dominates its first Fourier mode. -/
theorem sinc_first_mode_sq_le_circleSincSquareGap
    {Q R : ℝ} (hQ : 0 < Q) (hR : 0 < R) :
    (Real.sinc Q - Real.sinc R) ^ 2 ≤
      circleSincSquareGap Q R := by
  have hsum := summable_circleSincSquareGapTerm hQ hR
  have hterm : circleSincSquareGapTerm Q R 0 ≤
      circleSincSquareGap Q R := by
    unfold circleSincSquareGap
    exact hsum.le_tsum 0 fun n hn ↦ by
      unfold circleSincSquareGapTerm
      positivity
  simpa [circleSincSquareGapTerm] using! hterm

/-- Exact derivative identity for the affine scalar. -/
theorem hasDerivAt_affineCircleScalar
    {H aPi bPi Ceff Rmax Qmax Q : ℝ} (hQ : 0 < Q) :
    HasDerivAt
      (affineCircleScalar H aPi bPi Ceff Rmax Qmax)
      (affineCircleScalarDerivative aPi Ceff Rmax Q) Q := by
  have hpenalty : HasDerivAt
      (fun x : ℝ ↦ circleEffectivePenalty aPi Ceff / x)
      (-circleEffectivePenalty aPi Ceff / Q ^ 2) Q := by
    convert! ((hasDerivAt_const Q (circleEffectivePenalty aPi Ceff)).div
      (hasDerivAt_id Q) hQ.ne') using 1
    simp [id_eq]
  have hsquare : HasDerivAt
      (fun x : ℝ ↦ (Real.sinc x - Real.sinc Rmax) ^ 2)
      (2 * (Real.sinc Q - Real.sinc Rmax) *
        (-sincNumerator Q / Q ^ 2)) Q := by
    convert! ((hasDerivAt_sinc_of_pos hQ).sub_const
      (Real.sinc Rmax)).pow 2 using 1
    ring
  have h := ((hasDerivAt_const Q
    (circleRectangleBase H aPi bPi Qmax Rmax)).add hpenalty).add hsquare
  convert! h using 1
  unfold affineCircleScalarDerivative
  field_simp [hQ.ne']
  ring

/-- Keeping the first Fourier square and moving both self-gaps to their
rectangle endpoints gives the scalar used in the finite verifier. -/
theorem retainedSquare_lower_bound_circleBlockMargin
    {H aPi bPi Ceff Q R Qmax Rmax : ℝ}
    (haPi : 0 < aPi)
    (hQ : 0 < Q) (hQmax : Q ≤ Qmax) (hQmaxPi : Qmax ≤ Real.pi)
    (hR : 0 < R) (hRmax : R ≤ Rmax) (hRmaxPi : Rmax ≤ Real.pi) :
    circleRectangleBase H aPi bPi Qmax Rmax +
        circleEffectivePenalty aPi Ceff / Q +
          (Real.sinc Q - Real.sinc R) ^ 2 ≤
      circleBlockMargin H aPi bPi Ceff Q R := by
  have hQmax0 : 0 < Qmax := hQ.trans_le hQmax
  have hRmax0 : 0 < Rmax := hR.trans_le hRmax
  have hcorrectionQ : circleCorrection Qmax ≤ circleCorrection Q :=
    circleCorrection_antitoneOn
      ⟨hQ, hQmax.trans hQmaxPi⟩ ⟨hQmax0, hQmaxPi⟩ hQmax
  have hcorrectionR : circleCorrection Rmax ≤ circleCorrection R :=
    circleCorrection_antitoneOn
      ⟨hR, hRmax.trans hRmaxPi⟩ ⟨hRmax0, hRmaxPi⟩ hRmax
  have hsquare := sinc_first_mode_sq_le_circleSincSquareGap hQ hR
  calc
    circleRectangleBase H aPi bPi Qmax Rmax +
          circleEffectivePenalty aPi Ceff / Q +
            (Real.sinc Q - Real.sinc R) ^ 2 ≤
        Real.log (2 * H / (aPi * bPi)) +
          circleCorrection Q + circleCorrection R +
            circleSincSquareGap Q R +
              circleEffectivePenalty aPi Ceff / Q := by
      unfold circleRectangleBase
      linarith
    _ = circleBlockMargin H aPi bPi Ceff Q R := by
      unfold circleBlockMargin circleEffectivePenalty
      field_simp [haPi.ne', hQ.ne']
      ring

/-- Exact certificate interface for the constant-edge rows of the parameter
cover.  Only one endpoint scalar remains to be checked on each `k` slab. -/
structure ConstantEdgeCircleCertificate
    (H aPi bPi Ceff Qmax Rmax : ℝ) : Prop where
  aPi_pos : 0 < aPi
  Qmax_pos : 0 < Qmax
  Qmax_le_pi : Qmax ≤ Real.pi
  Rmax_pos : 0 < Rmax
  Rmax_le_pi : Rmax ≤ Real.pi
  Ceff_nonpos : Ceff ≤ 0
  endpoint_pos :
    0 < circleRectangleBase H aPi bPi Qmax Rmax +
      circleEffectivePenalty aPi Ceff / Qmax

/-- A constant-edge certificate proves strict positivity on the entire mass
rectangle, not merely on the finitely many parameter endpoints. -/
theorem circleBlockMargin_pos_of_constantEdgeCertificate
    {H aPi bPi Ceff Qmax Rmax Q R : ℝ}
    (hcert : ConstantEdgeCircleCertificate
      H aPi bPi Ceff Qmax Rmax)
    (hQ : 0 < Q) (hQmax : Q ≤ Qmax)
    (hR : 0 < R) (hRmax : R ≤ Rmax) :
    0 < circleBlockMargin H aPi bPi Ceff Q R := by
  have hpenalty : 0 ≤ circleEffectivePenalty aPi Ceff := by
    unfold circleEffectivePenalty
    exact div_nonneg
      (mul_nonneg_of_nonpos_of_nonpos
        (neg_nonpos.mpr Real.pi_pos.le) hcert.Ceff_nonpos)
      hcert.aPi_pos.le
  have hpenaltyMono :
      circleEffectivePenalty aPi Ceff / Qmax ≤
        circleEffectivePenalty aPi Ceff / Q := by
    rw [div_le_div_iff₀ hcert.Qmax_pos hQ]
    nlinarith [mul_nonneg hpenalty (sub_nonneg.mpr hQmax)]
  have hlower := retainedSquare_lower_bound_circleBlockMargin
    (H := H) (bPi := bPi) (Ceff := Ceff)
    hcert.aPi_pos hQ hQmax hcert.Qmax_le_pi
      hR hRmax hcert.Rmax_le_pi
  have hsquare : 0 ≤ (Real.sinc Q - Real.sinc R) ^ 2 := sq_nonneg _
  linarith [hcert.endpoint_pos]

/-- Terminal certificate used when `Ceff ≤ 0`: the favorable effective
term may be discarded, so positivity of the base scalar alone controls the
whole rectangle. -/
structure TerminalCircleCertificate
    (H aPi bPi Ceff Qmax Rmax : ℝ) : Prop where
  aPi_pos : 0 < aPi
  Qmax_pos : 0 < Qmax
  Qmax_le_pi : Qmax ≤ Real.pi
  Rmax_pos : 0 < Rmax
  Rmax_le_pi : Rmax ≤ Real.pi
  Ceff_nonpos : Ceff ≤ 0
  base_pos : 0 < circleRectangleBase H aPi bPi Qmax Rmax

theorem circleBlockMargin_pos_of_terminalCertificate
    {H aPi bPi Ceff Qmax Rmax Q R : ℝ}
    (hcert : TerminalCircleCertificate H aPi bPi Ceff Qmax Rmax)
    (hQ : 0 < Q) (hQmax : Q ≤ Qmax)
    (hR : 0 < R) (hRmax : R ≤ Rmax) :
    0 < circleBlockMargin H aPi bPi Ceff Q R := by
  have hpenalty : 0 ≤ circleEffectivePenalty aPi Ceff := by
    unfold circleEffectivePenalty
    exact div_nonneg
      (mul_nonneg_of_nonpos_of_nonpos
        (neg_nonpos.mpr Real.pi_pos.le) hcert.Ceff_nonpos)
      hcert.aPi_pos.le
  have hpenaltyQ : 0 ≤ circleEffectivePenalty aPi Ceff / Q :=
    div_nonneg hpenalty hQ.le
  have hlower := retainedSquare_lower_bound_circleBlockMargin
    (H := H) (bPi := bPi) (Ceff := Ceff)
    hcert.aPi_pos hQ hQmax hcert.Qmax_le_pi
      hR hRmax hcert.Rmax_le_pi
  have hsquare : 0 ≤ (Real.sinc Q - Real.sinc R) ^ 2 := sq_nonneg _
  linarith [hcert.base_pos]

/-- The simple terminal verifier checks only the logarithmic prefactor.  The
two endpoint self-gaps are automatically nonnegative. -/
theorem terminalCircleCertificate_of_prefactor_pos
    {H aPi bPi Ceff Qmax Rmax : ℝ}
    (haPi : 0 < aPi)
    (hQmax : 0 < Qmax) (hQmaxPi : Qmax ≤ Real.pi)
    (hRmax : 0 < Rmax) (hRmaxPi : Rmax ≤ Real.pi)
    (hCeff : Ceff ≤ 0)
    (hprefactor : 0 < Real.log (2 * H / (aPi * bPi))) :
    TerminalCircleCertificate H aPi bPi Ceff Qmax Rmax := by
  refine ⟨haPi, hQmax, hQmaxPi, hRmax, hRmaxPi, hCeff, ?_⟩
  unfold circleRectangleBase
  have hQcorrection := circleCorrection_nonneg hQmax hQmaxPi
  have hRcorrection := circleCorrection_nonneg hRmax hRmaxPi
  linarith

/-- Exact certificate interface for the affine rows of the parameter cover.
The derivative field is precisely the sign checked on the 32 `Q` subcells. -/
structure AffineCircleCertificate
    (H aPi bPi Ceff Qmax Rmax : ℝ) : Prop where
  aPi_pos : 0 < aPi
  Rmax_pos : 0 < Rmax
  Rmax_lt_Qmax : Rmax < Qmax
  Qmax_le_pi : Qmax ≤ Real.pi
  Ceff_neg : Ceff < 0
  left_pos :
    0 < circleRectangleBase H aPi bPi Qmax Rmax +
      circleEffectivePenalty aPi Ceff / Rmax
  corner_pos : 0 < affineCircleScalar H aPi bPi Ceff Rmax Qmax Qmax
  derivative_neg : ∀ Q ∈ Ioo Rmax Qmax,
    affineCircleScalarDerivative aPi Ceff Rmax Q < 0

theorem affineCircleScalar_antitoneOn_of_certificate
    {H aPi bPi Ceff Qmax Rmax : ℝ}
    (hcert : AffineCircleCertificate H aPi bPi Ceff Qmax Rmax) :
    AntitoneOn (affineCircleScalar H aPi bPi Ceff Rmax Qmax)
      (Icc Rmax Qmax) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc Rmax Qmax)
  · intro Q hQ
    exact (hasDerivAt_affineCircleScalar
      (hcert.Rmax_pos.trans_le hQ.1)).continuousAt.continuousWithinAt
  · intro Q hQ
    rw [interior_Icc] at hQ
    exact (hasDerivAt_affineCircleScalar
      (hcert.Rmax_pos.trans hQ.1)).hasDerivWithinAt
  · intro Q hQ
    rw [interior_Icc] at hQ
    exact (hcert.derivative_neg Q hQ).le

theorem affineCircleScalar_pos_of_certificate
    {H aPi bPi Ceff Qmax Rmax Q : ℝ}
    (hcert : AffineCircleCertificate H aPi bPi Ceff Qmax Rmax)
    (hQ : Q ∈ Icc Rmax Qmax) :
    0 < affineCircleScalar H aPi bPi Ceff Rmax Qmax Q := by
  have hmono := affineCircleScalar_antitoneOn_of_certificate hcert
    hQ ⟨hcert.Rmax_lt_Qmax.le, le_rfl⟩ hQ.2
  exact hcert.corner_pos.trans_le hmono

/-- An affine certificate proves strict positivity on the entire mass
rectangle.  This is the exact two-case reduction in manuscript (7.9)--(7.10). -/
theorem circleBlockMargin_pos_of_affineCertificate
    {H aPi bPi Ceff Qmax Rmax Q R : ℝ}
    (hcert : AffineCircleCertificate H aPi bPi Ceff Qmax Rmax)
    (hQ : 0 < Q) (hQmax : Q ≤ Qmax)
    (hR : 0 < R) (hRmax : R ≤ Rmax) :
    0 < circleBlockMargin H aPi bPi Ceff Q R := by
  have hRmaxPi : Rmax ≤ Real.pi :=
    hcert.Rmax_lt_Qmax.le.trans hcert.Qmax_le_pi
  have hpenalty : 0 < circleEffectivePenalty aPi Ceff := by
    unfold circleEffectivePenalty
    exact div_pos
      (mul_pos_of_neg_of_neg (neg_neg_of_pos Real.pi_pos) hcert.Ceff_neg)
      hcert.aPi_pos
  have hlower := retainedSquare_lower_bound_circleBlockMargin
    (H := H) (bPi := bPi) (Ceff := Ceff)
    hcert.aPi_pos hQ hQmax hcert.Qmax_le_pi
      hR hRmax hRmaxPi
  by_cases hQR : Q ≤ Rmax
  · have hpenaltyMono :
        circleEffectivePenalty aPi Ceff / Rmax ≤
          circleEffectivePenalty aPi Ceff / Q := by
      rw [div_le_div_iff₀ hcert.Rmax_pos hQ]
      nlinarith [mul_nonneg hpenalty.le (sub_nonneg.mpr hQR)]
    have hsquare : 0 ≤ (Real.sinc Q - Real.sinc R) ^ 2 := sq_nonneg _
    linarith [hcert.left_pos]
  · have hRmaxQ : Rmax < Q := lt_of_not_ge hQR
    have hscalar := affineCircleScalar_pos_of_certificate hcert
      ⟨hRmaxQ.le, hQmax⟩
    have hsincQRmax : Real.sinc Q ≤ Real.sinc Rmax :=
      sinc_antitoneOn_Icc_zero_pi
        ⟨hcert.Rmax_pos.le, hRmaxPi⟩
        ⟨hQ.le, hQmax.trans hcert.Qmax_le_pi⟩ hRmaxQ.le
    have hsincRmaxR : Real.sinc Rmax ≤ Real.sinc R :=
      sinc_antitoneOn_Icc_zero_pi
        ⟨hR.le, hRmax.trans hRmaxPi⟩
        ⟨hcert.Rmax_pos.le, hRmaxPi⟩ hRmax
    have hnonnegSmall : 0 ≤ Real.sinc Rmax - Real.sinc Q :=
      sub_nonneg.mpr hsincQRmax
    have hnonnegLarge : 0 ≤ Real.sinc R - Real.sinc Q :=
      sub_nonneg.mpr (hsincQRmax.trans hsincRmaxR)
    have hdiff : Real.sinc Rmax - Real.sinc Q ≤
        Real.sinc R - Real.sinc Q := sub_le_sub_right hsincRmaxR _
    have hsquare :
        (Real.sinc Q - Real.sinc Rmax) ^ 2 ≤
          (Real.sinc Q - Real.sinc R) ^ 2 := by
      have hsq := (sq_le_sq₀ hnonnegSmall hnonnegLarge).2 hdiff
      nlinarith
    unfold affineCircleScalar at hscalar
    linarith

/-! ## Exact caps for concrete platform interval radii -/

/-- The full reference normalized mass is the exact cap `π / a_π`. -/
def platformReferenceCircleRadiusCap (k a : ℝ) : ℝ :=
  Real.pi / platformAPi k a

/-- The full adjoint normalized mass is the exact cap `π R₀ / b_π`. -/
def platformAdjointCircleRadiusCap
    (a xMinus xPlus sigmaMinus sigmaPlus : ℝ) : ℝ :=
  Real.pi * platformAdjointMass
      a xMinus xPlus sigmaMinus sigmaPlus /
    platformBPi a xMinus xPlus sigmaMinus sigmaPlus

theorem platformReferenceCircleRadius_le_cap
    {k a left right : ℝ}
    (hk : 0 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    (hleft : 0 ≤ left) (hle : left ≤ right)
    (hright : right ≤ Real.pi) :
    platformReferenceCircleRadius k a left right ≤
      platformReferenceCircleRadiusCap k a := by
  have hnonneg : 0 ≤ᵐ[
      volume.restrict (Ioc (0 : ℝ) Real.pi)]
      platformNormalizedReferenceDensity k a := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with theta htheta
    exact (platformNormalizedReferenceDensity_mem_Icc
      hk ha ha2.le hthreshold ⟨htheta.1.le, htheta.2⟩).1
  unfold platformReferenceCircleRadius platformReferenceCircleRadiusCap
  calc
    (∫ theta : ℝ in left..right,
        platformNormalizedReferenceDensity k a theta) ≤
        ∫ theta : ℝ in 0..Real.pi,
          platformNormalizedReferenceDensity k a theta :=
      intervalIntegral.integral_mono_interval
        hleft hle hright hnonneg
          (intervalIntegrable_platformNormalizedReferenceDensity
            k ha ha2.le)
    _ = Real.pi / platformAPi k a :=
      integral_platformNormalizedReferenceDensity k ha ha2.le

theorem platformAdjointCircleRadius_le_cap
    {a xMinus xPlus sigmaMinus sigmaPlus left right : ℝ}
    (hxMinus : xMinus < a) (hxPlus : xPlus < a)
    (hsigmaMinus : 0 < sigmaMinus) (hsigmaPlus : 0 < sigmaPlus)
    (ha2 : a < 2) (hleft : 0 ≤ left) (hle : left ≤ right)
    (hright : right ≤ Real.pi) :
    platformAdjointCircleRadius
        a xMinus xPlus sigmaMinus sigmaPlus left right ≤
      platformAdjointCircleRadiusCap
        a xMinus xPlus sigmaMinus sigmaPlus := by
  have hnonneg : 0 ≤ᵐ[
      volume.restrict (Ioc (0 : ℝ) Real.pi)]
      platformNormalizedAdjointDensity
        a xMinus xPlus sigmaMinus sigmaPlus := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with theta htheta
    exact (platformNormalizedAdjointDensity_mem_Icc
      hxMinus hxPlus hsigmaMinus hsigmaPlus ha2
        ⟨htheta.1.le, htheta.2⟩).1
  unfold platformAdjointCircleRadius platformAdjointCircleRadiusCap
  calc
    (∫ theta : ℝ in left..right,
        platformNormalizedAdjointDensity
          a xMinus xPlus sigmaMinus sigmaPlus theta) ≤
        ∫ theta : ℝ in 0..Real.pi,
          platformNormalizedAdjointDensity
            a xMinus xPlus sigmaMinus sigmaPlus theta :=
      intervalIntegral.integral_mono_interval
        hleft hle hright hnonneg
          (intervalIntegrable_platformNormalizedAdjointDensity
            hxMinus hxPlus ha2)
    _ = Real.pi * platformAdjointMass
          a xMinus xPlus sigmaMinus sigmaPlus /
        platformBPi a xMinus xPlus sigmaMinus sigmaPlus :=
      integral_platformNormalizedAdjointDensity hxMinus hxPlus ha2

/-! ## Platform-specialized certificate interfaces -/

/-- The exact affine platform edge used on the first 264 slabs. -/
def affineHighKPlatformEdge (k : ℝ) : ℝ :=
  1153 / 500 - k / 4

/-- The exact constant platform edge used on the next 840 slabs. -/
def constantHighKPlatformEdge : ℝ :=
  9 / 5

/-- All elementary reference-side conditions on the affine edge are exact
consequences of the rational slab range.  They therefore do not belong in
the numerical certificate. -/
theorem affineHighKPlatformEdge_structural
    {k : ℝ} (hk : k ∈ Icc (36 / 25 : ℝ) (21 / 10)) :
    1 ≤ k ∧
      0 < affineHighKPlatformEdge k ∧
      affineHighKPlatformEdge k < 2 ∧
      platformThreshold k ≤ affineHighKPlatformEdge k := by
  have hk0 : 0 ≤ k := by linarith [hk.1]
  have hproduct : 0 ≤ k * (21 / 10 - k) :=
    mul_nonneg hk0 (sub_nonneg.mpr hk.2)
  have hedgeLower : (1781 / 1000 : ℝ) ≤ affineHighKPlatformEdge k := by
    unfold affineHighKPlatformEdge
    linarith [hk.2]
  have hthreshold : platformThreshold k ≤ affineHighKPlatformEdge k := by
    rw [platformThreshold_iff_square hk0]
    have hpositive :
        2 * k ^ 2 ≤ (1781 / 1000 : ℝ) * (k + 1) ^ 2 := by
      nlinarith
    have hsquare : 0 ≤ (k + 1) ^ 2 := sq_nonneg _
    nlinarith
  refine ⟨by linarith [hk.1], ?_, ?_, hthreshold⟩
  · linarith [hedgeLower]
  · unfold affineHighKPlatformEdge
    linarith [hk.1]

/-- All elementary reference-side conditions on the constant edge likewise
follow by rational arithmetic on the 840-slab range. -/
theorem constantHighKPlatformEdge_structural
    {k : ℝ} (hk : k ∈ Icc (21 / 10 : ℝ) (21 / 5)) :
    1 ≤ k ∧
      0 < constantHighKPlatformEdge ∧
      constantHighKPlatformEdge < 2 ∧
      platformThreshold k ≤ constantHighKPlatformEdge := by
  have hk0 : 0 ≤ k := by linarith [hk.1]
  have hproduct : 0 ≤ k * (21 / 5 - k) :=
    mul_nonneg hk0 (sub_nonneg.mpr hk.2)
  have hthreshold : platformThreshold k ≤ constantHighKPlatformEdge := by
    rw [platformThreshold_iff_square hk0]
    unfold constantHighKPlatformEdge
    nlinarith
  refine ⟨by linarith [hk.1], by norm_num [constantHighKPlatformEdge],
    by norm_num [constantHighKPlatformEdge], hthreshold⟩

/-- Constant-edge scalar certificate with every abstract parameter replaced
by its exact platform expression. -/
def PlatformConstantEdgeCalibration
    (k a xMinus xPlus sigmaMinus sigmaPlus Ceff : ℝ) : Prop :=
  ConstantEdgeCircleCertificate
    (platformCapacity a) (platformAPi k a)
    (platformBPi a xMinus xPlus sigmaMinus sigmaPlus) Ceff
    (platformReferenceCircleRadiusCap k a)
    (platformAdjointCircleRadiusCap
      a xMinus xPlus sigmaMinus sigmaPlus)

/-- Affine scalar certificate with every abstract parameter replaced by its
exact platform expression. -/
def PlatformAffineCalibration
    (k a xMinus xPlus sigmaMinus sigmaPlus Ceff : ℝ) : Prop :=
  AffineCircleCertificate
    (platformCapacity a) (platformAPi k a)
    (platformBPi a xMinus xPlus sigmaMinus sigmaPlus) Ceff
    (platformReferenceCircleRadiusCap k a)
    (platformAdjointCircleRadiusCap
      a xMinus xPlus sigmaMinus sigmaPlus)

/-- Terminal scalar certificate with exact platform parameters. -/
def PlatformTerminalCalibration
    (k a xMinus xPlus sigmaMinus sigmaPlus Ceff : ℝ) : Prop :=
  TerminalCircleCertificate
    (platformCapacity a) (platformAPi k a)
    (platformBPi a xMinus xPlus sigmaMinus sigmaPlus) Ceff
    (platformReferenceCircleRadiusCap k a)
    (platformAdjointCircleRadiusCap
      a xMinus xPlus sigmaMinus sigmaPlus)

theorem platformCircleBlockMargin_pos_of_constantEdgeCalibration
    {k a xMinus xPlus sigmaMinus sigmaPlus Ceff left right : ℝ}
    (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    (hxMinus : xMinus < a) (hxPlus : xPlus < a)
    (hsigmaMinus : 0 < sigmaMinus) (hsigmaPlus : 0 < sigmaPlus)
    (hleft : 0 ≤ left) (hlt : left < right)
    (hright : right ≤ Real.pi)
    (hcert : PlatformConstantEdgeCalibration
      k a xMinus xPlus sigmaMinus sigmaPlus Ceff) :
    0 < circleBlockMargin
      (platformCapacity a) (platformAPi k a)
      (platformBPi a xMinus xPlus sigmaMinus sigmaPlus) Ceff
      (platformReferenceCircleRadius k a left right)
      (platformAdjointCircleRadius
        a xMinus xPlus sigmaMinus sigmaPlus left right) := by
  have hk0 : 0 ≤ k := le_trans (by norm_num) hk
  apply circleBlockMargin_pos_of_constantEdgeCertificate hcert
  · exact platformReferenceCircleRadius_pos
      hk ha ha2 hthreshold hleft hlt hright
  · exact platformReferenceCircleRadius_le_cap
      hk0 ha ha2 hthreshold hleft hlt.le hright
  · exact platformAdjointCircleRadius_pos
      hxMinus hxPlus hsigmaMinus hsigmaPlus ha2 hleft hlt hright
  · exact platformAdjointCircleRadius_le_cap
      hxMinus hxPlus hsigmaMinus hsigmaPlus ha2 hleft hlt.le hright

theorem platformCircleBlockMargin_pos_of_affineCalibration
    {k a xMinus xPlus sigmaMinus sigmaPlus Ceff left right : ℝ}
    (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    (hxMinus : xMinus < a) (hxPlus : xPlus < a)
    (hsigmaMinus : 0 < sigmaMinus) (hsigmaPlus : 0 < sigmaPlus)
    (hleft : 0 ≤ left) (hlt : left < right)
    (hright : right ≤ Real.pi)
    (hcert : PlatformAffineCalibration
      k a xMinus xPlus sigmaMinus sigmaPlus Ceff) :
    0 < circleBlockMargin
      (platformCapacity a) (platformAPi k a)
      (platformBPi a xMinus xPlus sigmaMinus sigmaPlus) Ceff
      (platformReferenceCircleRadius k a left right)
      (platformAdjointCircleRadius
        a xMinus xPlus sigmaMinus sigmaPlus left right) := by
  have hk0 : 0 ≤ k := le_trans (by norm_num) hk
  apply circleBlockMargin_pos_of_affineCertificate hcert
  · exact platformReferenceCircleRadius_pos
      hk ha ha2 hthreshold hleft hlt hright
  · exact platformReferenceCircleRadius_le_cap
      hk0 ha ha2 hthreshold hleft hlt.le hright
  · exact platformAdjointCircleRadius_pos
      hxMinus hxPlus hsigmaMinus hsigmaPlus ha2 hleft hlt hright
  · exact platformAdjointCircleRadius_le_cap
      hxMinus hxPlus hsigmaMinus hsigmaPlus ha2 hleft hlt.le hright

theorem platformCircleBlockMargin_pos_of_terminalCalibration
    {k a xMinus xPlus sigmaMinus sigmaPlus Ceff left right : ℝ}
    (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    (hxMinus : xMinus < a) (hxPlus : xPlus < a)
    (hsigmaMinus : 0 < sigmaMinus) (hsigmaPlus : 0 < sigmaPlus)
    (hleft : 0 ≤ left) (hlt : left < right)
    (hright : right ≤ Real.pi)
    (hcert : PlatformTerminalCalibration
      k a xMinus xPlus sigmaMinus sigmaPlus Ceff) :
    0 < circleBlockMargin
      (platformCapacity a) (platformAPi k a)
      (platformBPi a xMinus xPlus sigmaMinus sigmaPlus) Ceff
      (platformReferenceCircleRadius k a left right)
      (platformAdjointCircleRadius
        a xMinus xPlus sigmaMinus sigmaPlus left right) := by
  have hk0 : 0 ≤ k := le_trans (by norm_num) hk
  apply circleBlockMargin_pos_of_terminalCertificate hcert
  · exact platformReferenceCircleRadius_pos
      hk ha ha2 hthreshold hleft hlt hright
  · exact platformReferenceCircleRadius_le_cap
      hk0 ha ha2 hthreshold hleft hlt.le hright
  · exact platformAdjointCircleRadius_pos
      hxMinus hxPlus hsigmaMinus hsigmaPlus ha2 hleft hlt hright
  · exact platformAdjointCircleRadius_le_cap
      hxMinus hxPlus hsigmaMinus hsigmaPlus ha2 hleft hlt.le hright

/-! ## Unconditional centered-energy bridge -/

/-- The centered two-arc deficit has exactly the self-energy plus Fourier
square normalization used by `circleBlockMargin`. -/
theorem normalizedCircleLogEnergy_twoArc_eq_self_add_gap
    {H Q R : ℝ} (hQ : 0 < Q) (hQpi : Q ≤ Real.pi)
    (hR : 0 < R) (hRpi : R ≤ Real.pi) :
    normalizedCircleLogEnergy H Q R (circleLogTwoArcEnergy Q R 0) =
      Real.log H + circleSelfEnergy Q + circleSelfEnergy R +
        circleSincSquareGap Q R := by
  rw [normalizedCircleLogEnergy,
    circleLogTwoArcEnergy_zero_toReal_eq_arcEnergy hQ hQpi hR hRpi,
    ← circleArcEnergy_self_eq_circleSelfEnergy hQ hQpi,
    ← circleArcEnergy_self_eq_circleSelfEnergy hR hRpi]
  have hsquare := circleArcEnergy_square_completion hQ hR
  field_simp [hQ.ne', hR.ne']
  linarith

/-- Rearrangement plus the exact centered Fourier evaluation supplies the
normalized block-energy hypothesis unconditionally for the concrete
platform deficit energy. -/
theorem circleSelfEnergy_add_gap_le_platformDeficitBlockEnergy_div
    {k a xMinus xPlus sigmaMinus sigmaPlus left right : ℝ}
    (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    (hxMinus : xMinus < a) (hxPlus : xPlus < a)
    (hsigmaMinus : 0 < sigmaMinus) (hsigmaPlus : 0 < sigmaPlus)
    (hleft : 0 ≤ left) (hlt : left < right)
    (hright : right ≤ Real.pi) :
    Real.log (platformCapacity a) +
          circleSelfEnergy (platformReferenceCircleRadius k a left right) +
          circleSelfEnergy (platformAdjointCircleRadius
            a xMinus xPlus sigmaMinus sigmaPlus left right) +
          circleSincSquareGap
            (platformReferenceCircleRadius k a left right)
            (platformAdjointCircleRadius
              a xMinus xPlus sigmaMinus sigmaPlus left right) ≤
      platformDeficitBlockEnergy
          k a xMinus xPlus sigmaMinus sigmaPlus left right /
        (platformReferenceIntervalMass k a left right *
          platformAdjointIntervalMass
            a xMinus xPlus sigmaMinus sigmaPlus left right) := by
  have hQ : 0 < platformReferenceCircleRadius k a left right :=
    platformReferenceCircleRadius_pos hk ha ha2 hthreshold
      hleft hlt hright
  have hR : 0 < platformAdjointCircleRadius
      a xMinus xPlus sigmaMinus sigmaPlus left right :=
    platformAdjointCircleRadius_pos hxMinus hxPlus
      hsigmaMinus hsigmaPlus ha2 hleft hlt hright
  have hQpi : platformReferenceCircleRadius k a left right ≤ Real.pi :=
    (platformReferenceCircleRadius_mem_Icc
      (le_trans (by norm_num) hk) ha ha2 hthreshold
        hleft hlt.le hright).2
  have hRpi : platformAdjointCircleRadius
      a xMinus xPlus sigmaMinus sigmaPlus left right ≤ Real.pi :=
    (platformAdjointCircleRadius_mem_Icc hxMinus hxPlus
      hsigmaMinus hsigmaPlus ha2 hleft hlt.le hright).2
  rw [← normalizedCircleLogEnergy_twoArc_eq_self_add_gap
    hQ hQpi hR hRpi]
  exact centered_normalizedCircleLogEnergy_le_deficitBlockEnergy_div
    hk ha ha2 hthreshold hxMinus hxPlus hsigmaMinus hsigmaPlus
      hleft hlt hright

/-- Strict platform block inequality.  This is the strict counterpart of
`platformCircleBlock_energy_bound_of_margin_nonneg`. -/
theorem platformCircleBlock_strict_energy_bound_of_margin_pos
    {k a xMinus xPlus sigmaMinus sigmaPlus left right Ceff E : ℝ}
    (hk : 0 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hxMinus : xMinus < a) (hxPlus : xPlus < a)
    (hsigmaMinus : 0 < sigmaMinus) (hsigmaPlus : 0 < sigmaPlus)
    (hQ : 0 < platformReferenceCircleRadius k a left right)
    (hR : 0 < platformAdjointCircleRadius
      a xMinus xPlus sigmaMinus sigmaPlus left right)
    (henergy :
      Real.log (platformCapacity a) +
          circleSelfEnergy (platformReferenceCircleRadius k a left right) +
          circleSelfEnergy (platformAdjointCircleRadius
            a xMinus xPlus sigmaMinus sigmaPlus left right) +
          circleSincSquareGap
            (platformReferenceCircleRadius k a left right)
            (platformAdjointCircleRadius
              a xMinus xPlus sigmaMinus sigmaPlus left right) ≤
        E /
          (platformReferenceIntervalMass k a left right *
            platformAdjointIntervalMass
              a xMinus xPlus sigmaMinus sigmaPlus left right))
    (hmargin : 0 < circleBlockMargin
      (platformCapacity a) (platformAPi k a)
      (platformBPi a xMinus xPlus sigmaMinus sigmaPlus) Ceff
      (platformReferenceCircleRadius k a left right)
      (platformAdjointCircleRadius
        a xMinus xPlus sigmaMinus sigmaPlus left right)) :
    platformReferenceIntervalMass k a left right *
          platformAdjointIntervalMass
            a xMinus xPlus sigmaMinus sigmaPlus left right *
          Real.log
            (platformReferenceIntervalMass k a left right *
                platformAdjointIntervalMass
                  a xMinus xPlus sigmaMinus sigmaPlus left right /
              2) +
        Ceff * platformAdjointIntervalMass
          a xMinus xPlus sigmaMinus sigmaPlus left right < E := by
  apply circleBlock_strict_energy_bound_of_margin_pos
    (platformCapacity_pos ha2)
    (platformAPi_pos hk ha ha2.le)
    (platformBPi_pos hxMinus hxPlus hsigmaMinus hsigmaPlus ha2)
    hQ hR
  · exact platformReferenceIntervalMass_eq_endpoint_mul_radius hk ha ha2.le
  · exact platformAdjointIntervalMass_eq_endpoint_mul_radius
      hxMinus hxPlus hsigmaMinus hsigmaPlus ha2
  · exact henergy
  · exact hmargin

/-- For the concrete deficit energy the normalized-energy premise is now a
theorem, so strictness of a platform block depends only on its scalar
margin. -/
theorem platformCircleBlock_strict_deficitEnergy_bound_of_margin_pos
    {k a xMinus xPlus sigmaMinus sigmaPlus left right Ceff : ℝ}
    (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    (hxMinus : xMinus < a) (hxPlus : xPlus < a)
    (hsigmaMinus : 0 < sigmaMinus) (hsigmaPlus : 0 < sigmaPlus)
    (hleft : 0 ≤ left) (hlt : left < right)
    (hright : right ≤ Real.pi)
    (hmargin : 0 < circleBlockMargin
      (platformCapacity a) (platformAPi k a)
      (platformBPi a xMinus xPlus sigmaMinus sigmaPlus) Ceff
      (platformReferenceCircleRadius k a left right)
      (platformAdjointCircleRadius
        a xMinus xPlus sigmaMinus sigmaPlus left right)) :
    platformReferenceIntervalMass k a left right *
          platformAdjointIntervalMass
            a xMinus xPlus sigmaMinus sigmaPlus left right *
          Real.log
            (platformReferenceIntervalMass k a left right *
                platformAdjointIntervalMass
                  a xMinus xPlus sigmaMinus sigmaPlus left right /
              2) +
        Ceff * platformAdjointIntervalMass
          a xMinus xPlus sigmaMinus sigmaPlus left right <
      platformDeficitBlockEnergy
        k a xMinus xPlus sigmaMinus sigmaPlus left right := by
  have hQ := platformReferenceCircleRadius_pos
    hk ha ha2 hthreshold hleft hlt hright
  have hR := platformAdjointCircleRadius_pos
    hxMinus hxPlus hsigmaMinus hsigmaPlus ha2 hleft hlt hright
  exact platformCircleBlock_strict_energy_bound_of_margin_pos
    (le_trans (by norm_num) hk) ha ha2 hxMinus hxPlus
      hsigmaMinus hsigmaPlus hQ hR
      (circleSelfEnergy_add_gap_le_platformDeficitBlockEnergy_div
        hk ha ha2 hthreshold hxMinus hxPlus hsigmaMinus hsigmaPlus
          hleft hlt hright)
      hmargin

/-! ## Strict finite assembly -/

theorem blockRadiusExpression_strict_of_energy_bound
    {q r C Ceff E R : ℝ}
    (hq : 0 < q) (hr : 0 < r) (hR : 0 < R)
    (henergy : q * r * Real.log (q * r / 2) + Ceff * r < E) :
    (Ceff - C) * r < blockRadiusExpression q r C E R := by
  have hmin := block_radius_minimum (C := C) (E := E) hq hr hR
  linarith

theorem finite_block_reduction_strict
    {iota : Type*} [Fintype iota] [Nonempty iota]
    (q r E R : iota → ℝ) {C Ceff M0 L R0 : ℝ}
    (hq : ∀ i, 0 < q i) (hr : ∀ i, 0 < r i)
    (hR : ∀ i, 0 < R i)
    (hrsum : ∑ i, r i = R0)
    (henergy : ∀ i,
      q i * r i * Real.log (q i * r i / 2) + Ceff * r i < E i)
    (hcalibration : M0 + (Ceff - C) * R0 = L) :
    L < M0 + ∑ i, blockRadiusExpression (q i) (r i) C (E i) (R i) := by
  have hsum :
      ∑ i, (Ceff - C) * r i <
        ∑ i, blockRadiusExpression (q i) (r i) C (E i) (R i) := by
    apply Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
    intro i _hi
    exact blockRadiusExpression_strict_of_energy_bound
      (hq i) (hr i) (hR i) (henergy i)
  rw [← Finset.mul_sum, hrsum] at hsum
  linarith

/-- Strict finite platform assembly, conditional only on the normalized
centered-circle energy estimate and a strict scalar margin. -/
theorem finite_platformCircleBlock_strict_reduction
    {iota : Type*} [Fintype iota] [Nonempty iota]
    (left right energy targetRadius : iota → ℝ)
    {k a xMinus xPlus sigmaMinus sigmaPlus Ceff M0 L R0 : ℝ}
    (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    (hxMinus : xMinus < a) (hxPlus : xPlus < a)
    (hsigmaMinus : 0 < sigmaMinus) (hsigmaPlus : 0 < sigmaPlus)
    (hleft : ∀ i, 0 ≤ left i) (hlr : ∀ i, left i < right i)
    (hright : ∀ i, right i ≤ Real.pi)
    (hTargetRadius : ∀ i, 0 < targetRadius i)
    (hAdjointMassSum :
      ∑ i, platformAdjointIntervalMass
        a xMinus xPlus sigmaMinus sigmaPlus (left i) (right i) = R0)
    (henergy : ∀ i,
      Real.log (platformCapacity a) +
          circleSelfEnergy
            (platformReferenceCircleRadius k a (left i) (right i)) +
          circleSelfEnergy
            (platformAdjointCircleRadius a xMinus xPlus
              sigmaMinus sigmaPlus (left i) (right i)) +
          circleSincSquareGap
            (platformReferenceCircleRadius k a (left i) (right i))
            (platformAdjointCircleRadius a xMinus xPlus
              sigmaMinus sigmaPlus (left i) (right i)) ≤
        energy i /
          (platformReferenceIntervalMass k a (left i) (right i) *
            platformAdjointIntervalMass a xMinus xPlus
              sigmaMinus sigmaPlus (left i) (right i)))
    (hmargin : ∀ i, 0 < circleBlockMargin
      (platformCapacity a) (platformAPi k a)
      (platformBPi a xMinus xPlus sigmaMinus sigmaPlus) Ceff
      (platformReferenceCircleRadius k a (left i) (right i))
      (platformAdjointCircleRadius a xMinus xPlus
        sigmaMinus sigmaPlus (left i) (right i)))
    (hcalibration :
      M0 + (Ceff - platformPotentialConstant k a) * R0 = L) :
    L < M0 + ∑ i, blockRadiusExpression
      (platformReferenceIntervalMass k a (left i) (right i))
      (platformAdjointIntervalMass a xMinus xPlus
        sigmaMinus sigmaPlus (left i) (right i))
      (platformPotentialConstant k a) (energy i) (targetRadius i) := by
  have hk0 : 0 ≤ k := le_trans (by norm_num) hk
  let q : iota → ℝ := fun i ↦
    platformReferenceIntervalMass k a (left i) (right i)
  let r : iota → ℝ := fun i ↦
    platformAdjointIntervalMass a xMinus xPlus
      sigmaMinus sigmaPlus (left i) (right i)
  have hQ : ∀ i, 0 <
      platformReferenceCircleRadius k a (left i) (right i) := by
    intro i
    exact platformReferenceCircleRadius_pos hk ha ha2 hthreshold
      (hleft i) (hlr i) (hright i)
  have hR : ∀ i, 0 <
      platformAdjointCircleRadius a xMinus xPlus
        sigmaMinus sigmaPlus (left i) (right i) := by
    intro i
    exact platformAdjointCircleRadius_pos
      hxMinus hxPlus hsigmaMinus hsigmaPlus ha2
      (hleft i) (hlr i) (hright i)
  have hq : ∀ i, 0 < q i := by
    intro i
    dsimp only [q]
    rw [platformReferenceIntervalMass_eq_endpoint_mul_radius hk0 ha ha2.le]
    exact div_pos
      (mul_pos (platformAPi_pos hk0 ha ha2.le) (hQ i)) Real.pi_pos
  have hr : ∀ i, 0 < r i := by
    intro i
    dsimp only [r]
    rw [platformAdjointIntervalMass_eq_endpoint_mul_radius
      hxMinus hxPlus hsigmaMinus hsigmaPlus ha2]
    exact div_pos
      (mul_pos
        (platformBPi_pos hxMinus hxPlus hsigmaMinus hsigmaPlus ha2)
        (hR i)) Real.pi_pos
  have hblock : ∀ i,
      q i * r i * Real.log (q i * r i / 2) + Ceff * r i < energy i := by
    intro i
    dsimp only [q, r]
    exact platformCircleBlock_strict_energy_bound_of_margin_pos
      hk0 ha ha2 hxMinus hxPlus hsigmaMinus hsigmaPlus
      (hQ i) (hR i) (henergy i) (hmargin i)
  apply finite_block_reduction_strict q r energy targetRadius
    hq hr hTargetRadius
  · simpa only [r] using! hAdjointMassSum
  · exact hblock
  · exact hcalibration

/-- The constant-edge finite assembly no longer has a per-block scalar
hypothesis: one platform slab certificate supplies every block margin. -/
theorem finite_platformCircleBlock_strict_reduction_of_constantEdgeCalibration
    {iota : Type*} [Fintype iota] [Nonempty iota]
    (left right energy targetRadius : iota → ℝ)
    {k a xMinus xPlus sigmaMinus sigmaPlus Ceff M0 L R0 : ℝ}
    (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    (hxMinus : xMinus < a) (hxPlus : xPlus < a)
    (hsigmaMinus : 0 < sigmaMinus) (hsigmaPlus : 0 < sigmaPlus)
    (hleft : ∀ i, 0 ≤ left i) (hlr : ∀ i, left i < right i)
    (hright : ∀ i, right i ≤ Real.pi)
    (hTargetRadius : ∀ i, 0 < targetRadius i)
    (hAdjointMassSum :
      ∑ i, platformAdjointIntervalMass
        a xMinus xPlus sigmaMinus sigmaPlus (left i) (right i) = R0)
    (henergy : ∀ i,
      Real.log (platformCapacity a) +
          circleSelfEnergy
            (platformReferenceCircleRadius k a (left i) (right i)) +
          circleSelfEnergy
            (platformAdjointCircleRadius a xMinus xPlus
              sigmaMinus sigmaPlus (left i) (right i)) +
          circleSincSquareGap
            (platformReferenceCircleRadius k a (left i) (right i))
            (platformAdjointCircleRadius a xMinus xPlus
              sigmaMinus sigmaPlus (left i) (right i)) ≤
        energy i /
          (platformReferenceIntervalMass k a (left i) (right i) *
            platformAdjointIntervalMass a xMinus xPlus
              sigmaMinus sigmaPlus (left i) (right i)))
    (hcert : PlatformConstantEdgeCalibration
      k a xMinus xPlus sigmaMinus sigmaPlus Ceff)
    (hcalibration :
      M0 + (Ceff - platformPotentialConstant k a) * R0 = L) :
    L < M0 + ∑ i, blockRadiusExpression
      (platformReferenceIntervalMass k a (left i) (right i))
      (platformAdjointIntervalMass a xMinus xPlus
        sigmaMinus sigmaPlus (left i) (right i))
      (platformPotentialConstant k a) (energy i) (targetRadius i) := by
  apply finite_platformCircleBlock_strict_reduction
    left right energy targetRadius hk ha ha2 hthreshold
      hxMinus hxPlus hsigmaMinus hsigmaPlus hleft hlr hright
      hTargetRadius hAdjointMassSum henergy
  · intro i
    exact platformCircleBlockMargin_pos_of_constantEdgeCalibration
      hk ha ha2 hthreshold hxMinus hxPlus hsigmaMinus hsigmaPlus
      (hleft i) (hlr i) (hright i) hcert
  · exact hcalibration

/-- The affine finite assembly likewise replaces all per-block margin leaves
by the one finite slab certificate used by the numerical verifier. -/
theorem finite_platformCircleBlock_strict_reduction_of_affineCalibration
    {iota : Type*} [Fintype iota] [Nonempty iota]
    (left right energy targetRadius : iota → ℝ)
    {k a xMinus xPlus sigmaMinus sigmaPlus Ceff M0 L R0 : ℝ}
    (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    (hxMinus : xMinus < a) (hxPlus : xPlus < a)
    (hsigmaMinus : 0 < sigmaMinus) (hsigmaPlus : 0 < sigmaPlus)
    (hleft : ∀ i, 0 ≤ left i) (hlr : ∀ i, left i < right i)
    (hright : ∀ i, right i ≤ Real.pi)
    (hTargetRadius : ∀ i, 0 < targetRadius i)
    (hAdjointMassSum :
      ∑ i, platformAdjointIntervalMass
        a xMinus xPlus sigmaMinus sigmaPlus (left i) (right i) = R0)
    (henergy : ∀ i,
      Real.log (platformCapacity a) +
          circleSelfEnergy
            (platformReferenceCircleRadius k a (left i) (right i)) +
          circleSelfEnergy
            (platformAdjointCircleRadius a xMinus xPlus
              sigmaMinus sigmaPlus (left i) (right i)) +
          circleSincSquareGap
            (platformReferenceCircleRadius k a (left i) (right i))
            (platformAdjointCircleRadius a xMinus xPlus
              sigmaMinus sigmaPlus (left i) (right i)) ≤
        energy i /
          (platformReferenceIntervalMass k a (left i) (right i) *
            platformAdjointIntervalMass a xMinus xPlus
              sigmaMinus sigmaPlus (left i) (right i)))
    (hcert : PlatformAffineCalibration
      k a xMinus xPlus sigmaMinus sigmaPlus Ceff)
    (hcalibration :
      M0 + (Ceff - platformPotentialConstant k a) * R0 = L) :
    L < M0 + ∑ i, blockRadiusExpression
      (platformReferenceIntervalMass k a (left i) (right i))
      (platformAdjointIntervalMass a xMinus xPlus
        sigmaMinus sigmaPlus (left i) (right i))
      (platformPotentialConstant k a) (energy i) (targetRadius i) := by
  apply finite_platformCircleBlock_strict_reduction
    left right energy targetRadius hk ha ha2 hthreshold
      hxMinus hxPlus hsigmaMinus hsigmaPlus hleft hlr hright
      hTargetRadius hAdjointMassSum henergy
  · intro i
    exact platformCircleBlockMargin_pos_of_affineCalibration
      hk ha ha2 hthreshold hxMinus hxPlus hsigmaMinus hsigmaPlus
      (hleft i) (hlr i) (hright i) hcert
  · exact hcalibration

/-! ## Exact 264/840 rational slab covers -/

/-- Every point of a finite uniform real grid interval belongs to one of its
closed cells.  This is the exact combinatorial bridge from slab certificates
to a continuous parameter range. -/
theorem exists_uniformGrid_cell
    {start step : ℝ} {N : ℕ} (hstep : 0 < step) (hN : 0 < N)
    {x : ℝ} (hx : x ∈ Icc start (start + N * step)) :
    ∃ i : Fin N,
      x ∈ Icc (start + i * step) (start + (i + 1) * step) := by
  let y : ℝ := (x - start) / step
  have hy0 : 0 ≤ y := div_nonneg (sub_nonneg.mpr hx.1) hstep.le
  have hyN : y ≤ N := by
    rw [div_le_iff₀ hstep]
    linarith [hx.2]
  by_cases hyEq : y = N
  · let i : Fin N :=
      ⟨N - 1, Nat.sub_lt hN (by norm_num)⟩
    have hxy : x - start = N * step := by
      rw [← hyEq]
      dsimp only [y]
      field_simp [hstep.ne']
    refine ⟨i, ?_, ?_⟩
    · have hiN : (((N - 1 : ℕ) : ℝ)) ≤ N := by
        exact_mod_cast Nat.sub_le N 1
      change start + ((N - 1 : ℕ) : ℝ) * step ≤ x
      linarith [mul_le_mul_of_nonneg_right hiN hstep.le]
    · have hpred : N - 1 + 1 = N := Nat.succ_pred_eq_of_pos hN
      have hcast : ((N - 1 : ℕ) : ℝ) + 1 = (N : ℝ) := by
        exact_mod_cast hpred
      change x ≤ start + (((N - 1 : ℕ) : ℝ) + 1) * step
      rw [hcast]
      linarith
  · have hyLt : y < N := lt_of_le_of_ne hyN hyEq
    have hfloorLt : ⌊y⌋₊ < N := (Nat.floor_lt hy0).mpr hyLt
    let i : Fin N := ⟨⌊y⌋₊, hfloorLt⟩
    refine ⟨i, ?_⟩
    have hfloorLe : ((⌊y⌋₊ : ℕ) : ℝ) ≤ y := Nat.floor_le hy0
    have hySucc : y ≤ ((⌊y⌋₊ : ℕ) : ℝ) + 1 :=
      (Nat.lt_floor_add_one y).le
    have hxy : x - start = y * step := by
      dsimp only [y]
      field_simp [hstep.ne']
    rw [mem_Icc]
    constructor
    · dsimp only [i]
      nlinarith [mul_le_mul_of_nonneg_right hfloorLe hstep.le]
    · dsimp only [i]
      nlinarith [mul_le_mul_of_nonneg_right hySucc hstep.le]

/-- A proposition verified on all cells of a uniform grid holds on the whole
covered interval. -/
theorem of_forall_uniformGrid_cells
    {start step : ℝ} {N : ℕ} (hstep : 0 < step) (hN : 0 < N)
    {P : ℝ → Prop}
    (hcells : ∀ i : Fin N, ∀ x ∈
      Icc (start + i * step) (start + (i + 1) * step), P x) :
    ∀ x ∈ Icc start (start + N * step), P x := by
  intro x hx
  obtain ⟨i, hi⟩ := exists_uniformGrid_cell hstep hN hx
  exact hcells i x hi

/-- Exact affine grid used by the source verifier: 264 cells of width
`1/400`, beginning at `36/25` and ending at `21/10`. -/
def affineCalibrationSlab (i : Fin 264) : Set ℝ :=
  Icc (36 / 25 + i / 400) (36 / 25 + (i + 1) / 400)

/-- Exact constant-edge grid used by the source verifier: 840 cells of width
`1/400`, beginning at `21/10` and ending at `21/5`. -/
def constantEdgeCalibrationSlab (i : Fin 840) : Set ℝ :=
  Icc (21 / 10 + i / 400) (21 / 10 + (i + 1) / 400)

theorem affineCalibrationSlabs_cover
    {P : ℝ → Prop}
    (hcells : ∀ i : Fin 264, ∀ k ∈ affineCalibrationSlab i, P k) :
    ∀ k ∈ Icc (36 / 25 : ℝ) (21 / 10), P k := by
  have hcover := of_forall_uniformGrid_cells
    (start := (36 / 25 : ℝ)) (step := (1 / 400 : ℝ))
    (N := 264) (by norm_num) (by norm_num)
    (P := P) (by
      intro i x hx
      apply hcells i x
      simpa [affineCalibrationSlab, div_eq_mul_inv] using! hx)
  intro k hk
  apply hcover k
  convert! hk using 1
  norm_num

theorem constantEdgeCalibrationSlabs_cover
    {P : ℝ → Prop}
    (hcells : ∀ i : Fin 840, ∀ k ∈ constantEdgeCalibrationSlab i, P k) :
    ∀ k ∈ Icc (21 / 10 : ℝ) (21 / 5), P k := by
  have hcover := of_forall_uniformGrid_cells
    (start := (21 / 10 : ℝ)) (step := (1 / 400 : ℝ))
    (N := 840) (by norm_num) (by norm_num)
    (P := P) (by
      intro i x hx
      apply hcells i x
      simpa [constantEdgeCalibrationSlab, div_eq_mul_inv] using! hx)
  intro k hk
  apply hcover k
  convert! hk using 1
  norm_num

/-- A family of uniform affine slab certificates is exactly the continuous
calibration assertion needed by the platform block theorem. -/
theorem affinePlatformCalibration_of_slabCertificates
    (xMinus xPlus sigmaMinus sigmaPlus Ceff : ℝ → ℝ)
    (hcells : ∀ i : Fin 264, ∀ k ∈ affineCalibrationSlab i,
      PlatformAffineCalibration k (affineHighKPlatformEdge k)
        (xMinus k) (xPlus k) (sigmaMinus k) (sigmaPlus k) (Ceff k))
    {k : ℝ} (hk : k ∈ Icc (36 / 25 : ℝ) (21 / 10)) :
    PlatformAffineCalibration k (affineHighKPlatformEdge k)
      (xMinus k) (xPlus k) (sigmaMinus k) (sigmaPlus k) (Ceff k) := by
  exact affineCalibrationSlabs_cover hcells k hk

/-- A family of uniform constant-edge slab certificates supplies the whole
continuous second calibration range. -/
theorem constantPlatformCalibration_of_slabCertificates
    (xMinus xPlus sigmaMinus sigmaPlus Ceff : ℝ → ℝ)
    (hcells : ∀ i : Fin 840, ∀ k ∈ constantEdgeCalibrationSlab i,
      PlatformConstantEdgeCalibration k constantHighKPlatformEdge
        (xMinus k) (xPlus k) (sigmaMinus k) (sigmaPlus k) (Ceff k))
    {k : ℝ} (hk : k ∈ Icc (21 / 10 : ℝ) (21 / 5)) :
    PlatformConstantEdgeCalibration k constantHighKPlatformEdge
      (xMinus k) (xPlus k) (sigmaMinus k) (sigmaPlus k) (Ceff k) := by
  exact constantEdgeCalibrationSlabs_cover hcells k hk

/-- End-to-end affine range bridge from the 264 uniform certificate cells to
strict positivity of every nonempty platform circle block.  The elementary
reference conditions are discharged internally. -/
theorem affineHighKCircleBlockMargin_pos_of_slabCertificates
    (xMinus xPlus sigmaMinus sigmaPlus Ceff : ℝ → ℝ)
    (hcells : ∀ i : Fin 264, ∀ k ∈ affineCalibrationSlab i,
      PlatformAffineCalibration k (affineHighKPlatformEdge k)
        (xMinus k) (xPlus k) (sigmaMinus k) (sigmaPlus k) (Ceff k))
    {k left right : ℝ}
    (hk : k ∈ Icc (36 / 25 : ℝ) (21 / 10))
    (hxMinus : xMinus k < affineHighKPlatformEdge k)
    (hxPlus : xPlus k < affineHighKPlatformEdge k)
    (hsigmaMinus : 0 < sigmaMinus k) (hsigmaPlus : 0 < sigmaPlus k)
    (hleft : 0 ≤ left) (hlt : left < right) (hright : right ≤ Real.pi) :
    0 < circleBlockMargin
      (platformCapacity (affineHighKPlatformEdge k))
      (platformAPi k (affineHighKPlatformEdge k))
      (platformBPi (affineHighKPlatformEdge k) (xMinus k) (xPlus k)
        (sigmaMinus k) (sigmaPlus k)) (Ceff k)
      (platformReferenceCircleRadius k (affineHighKPlatformEdge k) left right)
      (platformAdjointCircleRadius (affineHighKPlatformEdge k)
        (xMinus k) (xPlus k) (sigmaMinus k) (sigmaPlus k) left right) := by
  obtain ⟨hk1, ha, ha2, hthreshold⟩ :=
    affineHighKPlatformEdge_structural hk
  exact platformCircleBlockMargin_pos_of_affineCalibration
    hk1 ha ha2 hthreshold hxMinus hxPlus hsigmaMinus hsigmaPlus
      hleft hlt hright
      (affinePlatformCalibration_of_slabCertificates
        xMinus xPlus sigmaMinus sigmaPlus Ceff hcells hk)

/-- End-to-end constant-edge bridge from the 840 uniform certificate cells
to strict positivity of every nonempty platform circle block. -/
theorem constantHighKCircleBlockMargin_pos_of_slabCertificates
    (xMinus xPlus sigmaMinus sigmaPlus Ceff : ℝ → ℝ)
    (hcells : ∀ i : Fin 840, ∀ k ∈ constantEdgeCalibrationSlab i,
      PlatformConstantEdgeCalibration k constantHighKPlatformEdge
        (xMinus k) (xPlus k) (sigmaMinus k) (sigmaPlus k) (Ceff k))
    {k left right : ℝ}
    (hk : k ∈ Icc (21 / 10 : ℝ) (21 / 5))
    (hxMinus : xMinus k < constantHighKPlatformEdge)
    (hxPlus : xPlus k < constantHighKPlatformEdge)
    (hsigmaMinus : 0 < sigmaMinus k) (hsigmaPlus : 0 < sigmaPlus k)
    (hleft : 0 ≤ left) (hlt : left < right) (hright : right ≤ Real.pi) :
    0 < circleBlockMargin
      (platformCapacity constantHighKPlatformEdge)
      (platformAPi k constantHighKPlatformEdge)
      (platformBPi constantHighKPlatformEdge (xMinus k) (xPlus k)
        (sigmaMinus k) (sigmaPlus k)) (Ceff k)
      (platformReferenceCircleRadius k constantHighKPlatformEdge left right)
      (platformAdjointCircleRadius constantHighKPlatformEdge
        (xMinus k) (xPlus k) (sigmaMinus k) (sigmaPlus k) left right) := by
  obtain ⟨hk1, ha, ha2, hthreshold⟩ :=
    constantHighKPlatformEdge_structural hk
  exact platformCircleBlockMargin_pos_of_constantEdgeCalibration
    hk1 ha ha2 hthreshold hxMinus hxPlus hsigmaMinus hsigmaPlus
      hleft hlt hright
      (constantPlatformCalibration_of_slabCertificates
        xMinus xPlus sigmaMinus sigmaPlus Ceff hcells hk)

end

end Erdos1038
