import ErdosProblems.Erdos67.MRGSA10FixedHighTailoredVertical
import ErdosProblems.Erdos67.MRGSA10FixedHighVerticalScalar

/-!
# Scalar higher-prime-power error for the tailored fixed-high contour

This is the clean handoff from the exact A.9/weighted-Schur contour theorem
to the eventual parameter schedule: the prime-energy term remains exact,
while the higher-prime-power correction is an explicit scalar.
-/

open scoped LSeries.notation

namespace Erdos67.MRHalaszBands

noncomputable section

/-- The source-tailored fixed-high contour bound with the full
higher-prime-power correction replaced by its source-square scalar. -/
theorem exists_norm_intervalIntegral_LSeries_gsA10SourceTailored_fixedHigh_scalar_le :
    ∃ Cβ : ℝ, 1 ≤ Cβ ∧
      ∀ {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
        (_hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
        (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂]
        {y A X Q S : ℕ} (_hy : 23 ≤ y) (_hX : 1 < X)
        (_hnonpret : MRArchimedeanNonpretentious f A X)
        (_hQ : 3 ≤ Q) (_hQy : Q ≤ y) (_hS : 101 ≤ S)
        (_hlogCβ : Real.log Cβ ≤ 2 * (S - 100 : ℕ) / 99)
        {alpha beta T : ℝ} (_hlogy : 6 ≤ Real.log (y : ℝ))
        (_halpha0 : 0 ≤ alpha)
        (_halpha : alpha ≤ (Real.log (y : ℝ))⁻¹)
        (_hbeta0 : 0 ≤ beta)
        (_hbeta : beta ≤ (Real.log (y : ℝ))⁻¹)
        (_hT : 0 < T) (_hTX : T ≤ X),
        ‖∫ t in -T..T,
            LSeries
              (gsA10SourceTailoredCoefficient
                f hmul P₁ P₂ y X alpha beta)
              (((Erdos67.EulerResidue.taoExponent X - alpha - 2 * beta : ℝ) : ℂ) +
                Complex.I * (t : ℂ))‖ ≤
          gsA10FixedHighHalaszEnvelope A X *
                (gsA10PrimeLambdaLeftEnergyBound Cβ Q S X y
                  (2 * beta) T) ^ ((1 : ℝ) / 2) *
              (gsA10PrimeLambdaRightEnergyBound Cβ Q S y X T) ^
                ((1 : ℝ) / 2) +
            2 * T * gsA10FixedHighHalaszEnvelope A X *
              ((X : ℝ) ^ (2 * (Real.log (y : ℝ))⁻¹) *
                (2 * gsA10PrimeLambdaHarmonicBudget X *
                    gsA10HigherPrimePowerGeometricMass y X +
                  (gsA10HigherPrimePowerGeometricMass y X) ^ 2)) := by
  obtain ⟨Cβ, hCβ, hmain⟩ :=
    exists_norm_intervalIntegral_LSeries_gsA10SourceTailored_fixedHigh_le
  refine ⟨Cβ, hCβ, ?_⟩
  intro f hmul hbound P₁ P₂ _ _ y A X Q S hy hX hnonpret hQ hQy hS
    hlogCβ alpha beta T hlogy halpha0 halpha hbeta0 hbeta hT hTX
  have hbase := hmain hmul hbound P₁ P₂ hy hX hnonpret hQ hQy hS
    hlogCβ hlogy halpha0 halpha hbeta0 hbeta hT hTX
  have hsplit := gsA10LambdaVerticalSplitError_fixedHigh_le
    (y := y) (X := X) (show 1 ≤ X by omega)
    (by linarith : 0 < Real.log (y : ℝ)) hbeta0 hbeta
  have hcoef : 0 ≤ 2 * T * gsA10FixedHighHalaszEnvelope A X :=
    mul_nonneg (mul_nonneg (by norm_num) hT.le)
      (gsA10FixedHighHalaszEnvelope_nonneg A X (by omega))
  exact hbase.trans (add_le_add_right
    (mul_le_mul_of_nonneg_left hsplit hcoef) _)

end

end Erdos67.MRHalaszBands

#print axioms
  Erdos67.MRHalaszBands.exists_norm_intervalIntegral_LSeries_gsA10SourceTailored_fixedHigh_scalar_le
