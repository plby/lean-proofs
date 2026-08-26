import ErdosProblems.Erdos67b.MRGSA10SourceContourLocalizedLocalHeight
import ErdosProblems.Erdos67b.MRGSA10SourceContourRow
import ErdosProblems.Erdos67b.MRGSA10SourcePerronIntegratedNorm

/-!
# Raw scheduled source Perron norm from local-height separation
-/

open Complex MeasureTheory Set

namespace Erdos67b.MRHalaszBands

noncomputable section

theorem exists_norm_gsA10TwoBlockSourcePerronIntegrated_le_rawSchedule_of_localHeight :
    ∃ Cbeta : ℝ, ∃ N : ℕ, 1 ≤ Cbeta ∧
      ∀ {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
        (_hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
        (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂]
        (_hsmallOutside : ∀ p ∈ gsA9SmallPrimeFinset, P₁ p)
        {A X y : ℕ},
        N ≤ y → 23 ≤ y → y ≤ X → 2 ≤ X → 2 ≤ X / y →
        4 ≤ Real.log (y : ℝ) → 1 ≤ Real.log (X : ℝ) →
        ∀ {eta T : ℝ},
        0 ≤ eta → eta ≤ (Real.log (y : ℝ))⁻¹ → eta ≤ 1 / 4 →
        1 ≤ T → 1 + Real.log (X : ℝ) ≤ T ^ 2 →
        (∀ u : ℝ, |u| ≤ T →
          (A : ℝ) ≤ pretentiousDistSq f (archimedeanTwist u) X) →
        ‖gsA10TwoBlockSourcePerronIntegrated
            f hmul P₁ P₂ y X eta T‖ / (X : ℝ) ≤
          2 *
            (((2 * Real.pi)⁻¹ * (3 * gsA9SmallPrimeEulerBound) *
                Real.exp
                  (28 * Real.exp 4 *
                      Erdos67b.EulerQuantitative.primeQuadraticConstant +
                    36 * gsA9SourceShiftConstant) * Real.exp 1) *
              (gsA10SourceMaximumModulusSqrtScalar A X /
                Real.sqrt (Real.log (X : ℝ))) *
              (2 *
                  (Real.exp 1 * Real.sqrt Real.pi *
                    (gsA10PrimeSourceAffineRowConstant Cbeta +
                      gsA10PrimeSourceAffineRowSlope Cbeta y X * T)) *
                  (2 * gsA10PrimeLambdaSymmetricBetaScalarConstant) +
                4 * T *
                  (2 * gsA10PrimeLambdaHarmonicBudget X *
                      gsA10HigherPrimePowerGeometricMass y X +
                    (gsA10HigherPrimePowerGeometricMass y X) ^ 2) * eta)) := by
  obtain ⟨Cbeta, N, hCbeta, hrow⟩ :=
    exists_sum_gsA10PrimeWindow_log_div_gaussian_sourceAffineRow
  refine ⟨Cbeta, N, hCbeta, ?_⟩
  intro f hmul hbound P₁ P₂ _ _ hsmallOutside A X y hNy hy23 hyX hX
    hquot hlogy hlogX eta T heta hetaY hetaQuarter hT hlogT hdist
  let J : ℝ :=
    ∫ alpha : ℝ in 0..eta,
      ∫ beta : ℝ in 0..eta,
        ‖gsA10TailoredPerronIntegral
            (gsA10TwoBlockAlternatingLow f P₁ P₂ y)
            (gsA9HighArithmetic f y)
            (gsA9HighGeneralizedMangoldt hmul y)
            y X (Erdos67b.EulerResidue.taoExponent X) alpha beta T‖
  let R : ℝ :=
    ((2 * Real.pi)⁻¹ * (3 * gsA9SmallPrimeEulerBound) *
        Real.exp
          (28 * Real.exp 4 *
              Erdos67b.EulerQuantitative.primeQuadraticConstant +
            36 * gsA9SourceShiftConstant) * Real.exp 1) *
      (gsA10SourceMaximumModulusSqrtScalar A X /
        Real.sqrt (Real.log (X : ℝ))) *
      (2 *
          (Real.exp 1 * Real.sqrt Real.pi *
            (gsA10PrimeSourceAffineRowConstant Cbeta +
              gsA10PrimeSourceAffineRowSlope Cbeta y X * T)) *
          (2 * gsA10PrimeLambdaSymmetricBetaScalarConstant) +
        4 * T *
          (2 * gsA10PrimeLambdaHarmonicBudget X *
              gsA10HigherPrimePowerGeometricMass y X +
            (gsA10HigherPrimePowerGeometricMass y X) ^ 2) * eta)
  have hArow : 0 ≤ gsA10PrimeSourceAffineRowConstant Cbeta :=
    gsA10PrimeSourceAffineRowConstant_nonneg hCbeta
  have hBrow : 0 ≤ gsA10PrimeSourceAffineRowSlope Cbeta y X :=
    gsA10PrimeSourceAffineRowSlope_nonneg hCbeta
      (show 1 ≤ y by omega) (show 1 ≤ X by omega)
  have hbase : (X : ℝ)⁻¹ * J ≤ R := by
    simpa only [J, R] using
      normalized_doubleIntervalIntegral_norm_sourceTailoredPerron_localHeight_le
        hmul hbound P₁ P₂ hsmallOutside hy23 hyX hX hquot hlogy hlogX
          heta hetaY hetaQuarter (zero_lt_one.trans_le hT) hlogT hdist
          hArow hBrow (hrow y X T hNy hT)
  have hnorm :
      ‖gsA10TwoBlockSourcePerronIntegrated
          f hmul P₁ P₂ y X eta T‖ ≤ 2 * J := by
    simpa only [J] using
      norm_gsA10TwoBlockSourcePerronIntegrated_le_doubleIntegral_norm
        hmul hbound P₁ P₂ hX hlogy heta hetaY (zero_le_one.trans hT)
  have hXpos : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  calc
    ‖gsA10TwoBlockSourcePerronIntegrated
        f hmul P₁ P₂ y X eta T‖ / (X : ℝ) =
        (X : ℝ)⁻¹ * ‖gsA10TwoBlockSourcePerronIntegrated
          f hmul P₁ P₂ y X eta T‖ := by ring
    _ ≤ (X : ℝ)⁻¹ * (2 * J) :=
      mul_le_mul_of_nonneg_left hnorm (inv_nonneg.mpr hXpos.le)
    _ = 2 * ((X : ℝ)⁻¹ * J) := by ring
    _ ≤ 2 * R := mul_le_mul_of_nonneg_left hbase (by norm_num)
    _ = _ := by rfl

end

end Erdos67b.MRHalaszBands

#print axioms
  Erdos67b.MRHalaszBands.exists_norm_gsA10TwoBlockSourcePerronIntegrated_le_rawSchedule_of_localHeight
