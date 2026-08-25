import ErdosProblems.Erdos67.MRGSA10DoubleIntegralMonoOn
import ErdosProblems.Erdos67.MRGSA10SourceContourLocalEnvelope
import ErdosProblems.Erdos67.MRGSA10SourceContourLocalIntegral
import ErdosProblems.Erdos67.MRGSA10SourceTailoredPerronContinuousOn

/-!
# Localized fixed-source contour integral

This replaces the global-continuity formulation by a direct comparison on
the source rectangle.  The analytic pointwise envelope and its scalar
integral are kept in separate compiled leaves, so elaboration stays within
the repository's default resource limits.
-/

open Complex MeasureTheory Set

namespace Erdos67.MRHalaszBands

noncomputable section

theorem normalized_doubleIntervalIntegral_norm_sourceTailoredPerron_local_le
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂]
    (hsmallOutside : ∀ p ∈ gsA9SmallPrimeFinset, P₁ p)
    {A X y : ℕ} (hy23 : 23 ≤ y) (hyX : y ≤ X) (hX : 2 ≤ X)
    (hN : 2 ≤ X / y) (hlogy : 4 ≤ Real.log (y : ℝ))
    (hlogX : 1 ≤ Real.log (X : ℝ))
    (hnonpret : MRArchimedeanNonpretentious f A X)
    {eta T Arow Brow : ℝ} (heta : 0 ≤ eta)
    (hetaY : eta ≤ (Real.log (y : ℝ))⁻¹)
    (hetaQuarter : eta ≤ 1 / 4)
    (hT0 : 0 < T) (hTX : T ≤ X)
    (hArow : 0 ≤ Arow) (hBrow : 0 ≤ Brow)
    (hrow : ∀ n ∈ gsA10PrimeWindow y X,
      (∑ m ∈ gsA10PrimeWindow y X,
          (Real.log (m : ℝ) / m) *
            finiteHalaszGaussianPairKernel (T⁻¹ ^ 2)
              (Real.log m - Real.log n)) ≤ Arow / T + Brow) :
    (X : ℝ)⁻¹ *
        (∫ alpha : ℝ in 0..eta,
          ∫ beta : ℝ in 0..eta,
            ‖gsA10TailoredPerronIntegral
                (gsA10TwoBlockAlternatingLow f P₁ P₂ y)
                (gsA9HighArithmetic f y)
                (gsA9HighGeneralizedMangoldt hmul y)
                y X (Erdos67.EulerResidue.taoExponent X)
                  alpha beta T‖) ≤
      ((2 * Real.pi)⁻¹ * (3 * gsA9SmallPrimeEulerBound) *
          Real.exp
            (28 * Real.exp 4 *
                Erdos67.EulerQuantitative.primeQuadraticConstant +
              36 * gsA9SourceShiftConstant) * Real.exp 1) *
        (gsA10SourceMaximumModulusSqrtScalar A X /
          Real.sqrt (Real.log (X : ℝ))) *
        (2 *
            (Real.exp 1 * Real.sqrt Real.pi * (Arow + Brow * T)) *
            (2 * gsA10PrimeLambdaSymmetricBetaScalarConstant) +
          4 * T *
            (2 * gsA10PrimeLambdaHarmonicBudget X *
                gsA10HigherPrimePowerGeometricMass y X +
              (gsA10HigherPrimePowerGeometricMass y X) ^ 2) * eta) := by
  let J : ℝ → ℝ → ℝ := fun alpha beta ↦
    ‖gsA10TailoredPerronIntegral
        (gsA10TwoBlockAlternatingLow f P₁ P₂ y)
        (gsA9HighArithmetic f y)
        (gsA9HighGeneralizedMangoldt hmul y)
        y X (Erdos67.EulerResidue.taoExponent X) alpha beta T‖
  let B : ℝ → ℝ → ℝ := fun alpha beta ↦
    gsA10SourceContourBetaPoleEnvelope A X y alpha beta T Arow Brow
  have hperronFull :=
    continuousOn_uncurry_gsA10SourceTailoredPerronIntegral_sourceRectangle
      hmul hbound P₁ P₂ hX hlogy hT0.le
  have hperron : ContinuousOn (Function.uncurry (fun alpha beta : ℝ ↦
      gsA10TailoredPerronIntegral
        (gsA10TwoBlockAlternatingLow f P₁ P₂ y)
        (gsA9HighArithmetic f y)
        (gsA9HighGeneralizedMangoldt hmul y)
        y X (Erdos67.EulerResidue.taoExponent X) alpha beta T))
      (Icc (0 : ℝ) eta ×ˢ Icc (0 : ℝ) eta) := by
    apply hperronFull.mono
    intro z hz
    exact ⟨⟨hz.1.1, hz.1.2.trans hetaY⟩,
      ⟨hz.2.1, hz.2.2.trans hetaY⟩⟩
  have hJ : ContinuousOn (Function.uncurry J)
      (Icc (0 : ℝ) eta ×ˢ Icc (0 : ℝ) eta) := by
    exact hperron.norm
  have hBfull := continuous_gsA10SourceContourBetaPoleEnvelope
    hX (show 0 < y by omega) hyX A T Arow Brow
  have hB : ContinuousOn (Function.uncurry B)
      (Icc (0 : ℝ) eta ×ˢ Icc (0 : ℝ) eta) := hBfull.continuousOn
  have hpoint : ∀ alpha ∈ Icc (0 : ℝ) eta,
      ∀ beta ∈ Icc (0 : ℝ) eta, J alpha beta ≤ B alpha beta := by
    intro alpha halpha beta hbeta
    dsimp only [J, B]
    exact norm_gsA10SourceTailoredPerronIntegral_le_betaPoleEnvelope
      hmul hbound P₁ P₂ hsmallOutside hy23 hyX hX hN hlogy hlogX
        hnonpret hetaY hetaQuarter hT0 hTX hArow hBrow hrow halpha hbeta
  have hmono :
      (∫ alpha : ℝ in 0..eta,
        ∫ beta : ℝ in 0..eta, J alpha beta) ≤
      ∫ alpha : ℝ in 0..eta,
        ∫ beta : ℝ in 0..eta, B alpha beta :=
    doubleIntervalIntegral_mono_continuousOn heta hJ hB hpoint
  have hscaled :
      (X : ℝ)⁻¹ *
          (∫ alpha : ℝ in 0..eta,
            ∫ beta : ℝ in 0..eta, J alpha beta) ≤
        (X : ℝ)⁻¹ *
          (∫ alpha : ℝ in 0..eta,
            ∫ beta : ℝ in 0..eta, B alpha beta) :=
    mul_le_mul_of_nonneg_left hmono (by positivity)
  have henvelope :=
    normalized_doubleIntervalIntegral_gsA10SourceContourBetaPoleEnvelope_le
      (A := A) (show 0 < y by omega) hyX hX heta hT0.le hArow hBrow
  calc
    _ = (X : ℝ)⁻¹ *
        (∫ alpha : ℝ in 0..eta,
          ∫ beta : ℝ in 0..eta, J alpha beta) := rfl
    _ ≤ (X : ℝ)⁻¹ *
        (∫ alpha : ℝ in 0..eta,
          ∫ beta : ℝ in 0..eta, B alpha beta) := hscaled
    _ ≤ _ := by simpa only [B] using henvelope

end

end Erdos67.MRHalaszBands

#print axioms
  Erdos67.MRHalaszBands.normalized_doubleIntervalIntegral_norm_sourceTailoredPerron_local_le
