import ErdosProblems.Erdos67b.MRGSA10SourceMaximumModulusLocalHeight
import ErdosProblems.Erdos67b.MRGSA10SourceFullVerticalContour

/-!
# Source A.10 vertical contour from local-height separation

This is the local-window counterpart of the source affine vertical estimate.
It retains the existing vertical budget verbatim, but needs distance only for
the frequencies actually integrated.
-/

open scoped LSeries.notation
open Complex Set MeasureTheory

namespace Erdos67b.MRHalaszBands

noncomputable section

/-- Fully source-shaped vertical estimate from local-height pretentious
separation. -/
theorem intervalIntegral_sourcePerronEnvelope_mul_lambdaPairNorm_le_affineRow_of_localHeight
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {A X y : ℕ} (hX : 2 ≤ X) (hy : 0 < y) (hyX : y ≤ X)
    (hN : 2 ≤ X / y) (hlogX : 1 ≤ Real.log (X : ℝ))
    {beta T Arow Brow : ℝ}
    (hbeta0 : 0 ≤ beta) (hbeta : beta ≤ 1 / 4)
    (hT0 : 0 < T)
    (hlogT : 1 + Real.log (X : ℝ) ≤ T ^ 2)
    (hdist : ∀ u : ℝ, |u| ≤ T →
      (A : ℝ) ≤ pretentiousDistSq f (archimedeanTwist u) X)
    (hArow : 0 ≤ Arow) (hBrow : 0 ≤ Brow)
    (hrow : ∀ n ∈ gsA10PrimeWindow y X,
      (∑ m ∈ gsA10PrimeWindow y X,
          (Real.log (m : ℝ) / m) *
            finiteHalaszGaussianPairKernel (T⁻¹ ^ 2)
              (Real.log m - Real.log n)) ≤ Arow / T + Brow) :
    (∫ t in -T..T,
      gsA10SourcePerronEnvelope f X beta t *
        gsA10SourceLambdaPairNorm f hmul y X beta t) ≤
      (Real.exp
          (28 * Real.exp 4 *
              Erdos67b.EulerQuantitative.primeQuadraticConstant +
            36 * gsA9SourceShiftConstant) *
        gsA10SourceMaximumModulusSqrtScalar A X *
        Real.sqrt
          ‖riemannZeta
            (((Erdos67b.EulerResidue.taoExponent X + beta : ℝ) : ℂ))‖) *
      (((X / y : ℕ) : ℝ) ^ beta *
        ((Real.exp 1 * Real.sqrt Real.pi * (Arow + Brow * T)) *
            gsA10PrimeLambdaSymmetricBetaDiagonalBudget X beta +
          2 * T *
            (2 * gsA10PrimeLambdaHarmonicBudget X *
                gsA10HigherPrimePowerGeometricMass y X +
              (gsA10HigherPrimePowerGeometricMass y X) ^ 2))) := by
  let M : ℝ :=
    Real.exp
        (28 * Real.exp 4 *
            Erdos67b.EulerQuantitative.primeQuadraticConstant +
          36 * gsA9SourceShiftConstant) *
      gsA10SourceMaximumModulusSqrtScalar A X *
      Real.sqrt
        ‖riemannZeta
          (((Erdos67b.EulerResidue.taoExponent X + beta : ℝ) : ℂ))‖
  let Q : ℝ := Real.exp 1 * Real.sqrt Real.pi * (Arow + Brow * T)
  let R : ℝ := ((X / y : ℕ) : ℝ) ^ beta
  let D : ℝ := gsA10PrimeLambdaSymmetricBetaDiagonalBudget X beta
  let E : ℝ := gsA10LambdaVerticalSplitError y X
    (Erdos67b.EulerResidue.taoExponent X - beta)
    (Erdos67b.EulerResidue.taoExponent X + beta)
  let G : ℝ :=
    2 * gsA10PrimeLambdaHarmonicBudget X *
        gsA10HigherPrimePowerGeometricMass y X +
      (gsA10HigherPrimePowerGeometricMass y X) ^ 2
  have hM0 : 0 ≤ M := by
    dsimp only [M, gsA10SourceMaximumModulusSqrtScalar]
    have hsqrt : 0 ≤ Real.sqrt (1 + Real.log (X : ℝ)) :=
      Real.sqrt_nonneg _
    positivity
  have henv : ∀ t, |t| ≤ T →
      gsA10SourcePerronEnvelope f X beta t ≤ M := by
    intro t ht
    simpa only [M] using
      (gsA10SourcePerronEnvelope_le_maximumModulus_of_localHeight
        hmul hbound (show 1 < X by omega) hlogX hT0 hlogT hdist
          hbeta0 hbeta ht)
  have hbase :=
    intervalIntegral_sourcePerronEnvelope_mul_lambdaPairNorm_le_uniform
      hmul hbound y hX hbeta0 hT0.le hM0 henv
  have hprime :=
    rpow_half_mul_intervalIntegral_normSq_gsA10PrimeLambda_tao_le_affineRow_symmetric
      hmul hbound y X beta T Arow Brow hX hN hbeta0
        (hbeta.trans (by norm_num : (1 / 4 : ℝ) ≤ 1 / 2))
        hT0 hArow hBrow hrow
  have hhpp := gsA10LambdaVerticalSplitError_symmetric_le
    hy hyX hX hbeta0
  change _ ≤ M * (_ + 2 * T * E) at hbase
  change _ ≤ Q * (R * D) at hprime
  change E ≤ R * G at hhpp
  change _ ≤ M * (R * (Q * D + 2 * T * G))
  calc
    _ ≤ M * (_ + 2 * T * E) := hbase
    _ ≤ M * (Q * (R * D) + 2 * T * (R * G)) := by
      gcongr
    _ = M * (R * (Q * D + 2 * T * G)) := by ring

/-- Actual restored source A.10 Perron contour, with the only distance
hypothesis localized to its height `T`. -/
theorem norm_gsA10SourceTailoredPerronIntegral_le_affineVerticalBudget_of_localHeight
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂]
    (hsmallOutside : ∀ p ∈ gsA9SmallPrimeFinset, P₁ p)
    {A X y : ℕ} (hy23 : 23 ≤ y) (hyX : y ≤ X) (hX : 2 ≤ X)
    (hN : 2 ≤ X / y) (hlogy : 4 ≤ Real.log (y : ℝ))
    (hlogX : 1 ≤ Real.log (X : ℝ))
    {alpha beta T Arow Brow : ℝ}
    (halpha0 : 0 ≤ alpha)
    (halpha : alpha ≤ (Real.log (y : ℝ))⁻¹)
    (hbeta0 : 0 ≤ beta)
    (hbetaY : beta ≤ (Real.log (y : ℝ))⁻¹)
    (hbeta : beta ≤ 1 / 4)
    (hT0 : 0 < T)
    (hlogT : 1 + Real.log (X : ℝ) ≤ T ^ 2)
    (hdist : ∀ u : ℝ, |u| ≤ T →
      (A : ℝ) ≤ pretentiousDistSq f (archimedeanTwist u) X)
    (hArow : 0 ≤ Arow) (hBrow : 0 ≤ Brow)
    (hrow : ∀ n ∈ gsA10PrimeWindow y X,
      (∑ m ∈ gsA10PrimeWindow y X,
          (Real.log (m : ℝ) / m) *
            finiteHalaszGaussianPairKernel (T⁻¹ ^ 2)
              (Real.log m - Real.log n)) ≤ Arow / T + Brow) :
    ‖gsA10TailoredPerronIntegral
        (gsA10TwoBlockAlternatingLow f P₁ P₂ y)
        (gsA9HighArithmetic f y)
        (gsA9HighGeneralizedMangoldt hmul y)
        y X (Erdos67b.EulerResidue.taoExponent X) alpha beta T‖ ≤
      (2 * Real.pi)⁻¹ *
        (3 * gsA9SmallPrimeEulerBound *
          (X : ℝ) ^
            (Erdos67b.EulerResidue.taoExponent X - alpha - beta)) *
        gsA10SourceAffineVerticalBudget A X y beta T Arow Brow := by
  let C : ℝ := 3 * gsA9SmallPrimeEulerBound *
    (X : ℝ) ^
      (Erdos67b.EulerResidue.taoExponent X - alpha - beta)
  let G : ℝ → ℝ := fun t ↦
    gsA10SourcePerronEnvelope f X beta t *
      gsA10SourceLambdaPairNorm f hmul y X beta t
  let V : ℝ := gsA10SourceAffineVerticalBudget A X y beta T Arow Brow
  have hbase :=
    norm_gsA10SourceTailoredPerronIntegral_le_weightedLambdaIntegral_continuous
      hmul hbound P₁ P₂ hsmallOutside hy23 (show 1 < X by omega)
        hlogy halpha0 halpha hbeta0 hbetaY hT0.le
  have hvertical : (∫ t in -T..T, G t) ≤ V := by
    dsimp only [G, V, gsA10SourceAffineVerticalBudget]
    exact
      intervalIntegral_sourcePerronEnvelope_mul_lambdaPairNorm_le_affineRow_of_localHeight
        hmul hbound hX (by omega) hyX hN hlogX hbeta0 hbeta hT0 hlogT
          hdist hArow hBrow hrow
  have hC0 : 0 ≤ C := by
    dsimp only [C]
    have hsmall0 : 0 ≤ gsA9SmallPrimeEulerBound := by
      have hsmall := norm_gsA9SmallPrimeEulerProduct_le hbound
        (sigma := (1 / 2 : ℝ)) (t := 0) le_rfl
      exact (norm_nonneg _).trans hsmall
    positivity
  have hpi0 : 0 ≤ (2 * Real.pi)⁻¹ :=
    inv_nonneg.mpr (by positivity)
  calc
    ‖gsA10TailoredPerronIntegral
        (gsA10TwoBlockAlternatingLow f P₁ P₂ y)
        (gsA9HighArithmetic f y)
        (gsA9HighGeneralizedMangoldt hmul y)
        y X (Erdos67b.EulerResidue.taoExponent X) alpha beta T‖ ≤
        (2 * Real.pi)⁻¹ * ∫ t in -T..T, C * G t := by
      simpa only [C, G, mul_assoc] using hbase
    _ = (2 * Real.pi)⁻¹ * (C * ∫ t in -T..T, G t) := by
      rw [intervalIntegral.integral_const_mul]
    _ ≤ (2 * Real.pi)⁻¹ * (C * V) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hvertical hC0) hpi0
    _ = _ := by
      dsimp only [C, V]
      ring

end

end Erdos67b.MRHalaszBands

#print axioms
  Erdos67b.MRHalaszBands.norm_gsA10SourceTailoredPerronIntegral_le_affineVerticalBudget_of_localHeight
