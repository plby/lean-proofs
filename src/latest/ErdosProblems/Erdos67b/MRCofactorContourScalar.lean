import ErdosProblems.Erdos67b.MRCofactorHigherPowerScalar
import ErdosProblems.Erdos67b.MRCofactorAverageEnvelopeScalar
import ErdosProblems.Erdos67b.MRCofactorRowHeight

/-! # Uniform scalar size of the averaged cofactor contour -/

namespace Erdos67b

open MRHalaszBands

noncomputable section

def mrCofactorContourScalarConstant : ℝ :=
  4 * (2 * Real.pi)⁻¹ * Real.exp 1 * mrCofactorAverageEnvelopeConstant

def mrCofactorContourMeanConstant (C : ℝ) : ℝ :=
  mrCofactorContourScalarConstant *
    (10 * gsA10SmallPowerSourceRowBound C * gsA10PrimeLambdaHarmonicLogConstant +
      gsA10SourceHPPRectangleBound)

theorem mrCofactorContourScalarConstant_nonneg : 0 ≤ mrCofactorContourScalarConstant := by
  unfold mrCofactorContourScalarConstant mrCofactorAverageEnvelopeConstant mrCofactorEulerBaseConstant
  positivity

theorem mrCofactorContourMeanConstant_nonneg {C : ℝ} (hC : 1 ≤ C) :
    0 ≤ mrCofactorContourMeanConstant C := by
  have hrow := gsA10SmallPowerSourceRowBound_nonneg hC
  have hH := gsA10PrimeLambdaHarmonicLogConstant_nonneg
  have hB := gsA10SourceHPPRectangleBound_nonneg
  exact mul_nonneg mrCofactorContourScalarConstant_nonneg (by positivity)

theorem mrCofactor_contourBudget_le_scalar {C : ℝ} (hC : 1 ≤ C) {N y X : ℕ}
    (hN : 0 < N) (hX : 4 ≤ X) (hy : 3 ≤ y) (hlogX : 1 ≤ Real.log (X : ℝ))
    (hprime : PrimeEstimates.primeReciprocals X ≤ Real.log (X : ℝ))
    (hlogSquare : 4 * Real.log (X : ℝ) ≤ Real.log (y : ℝ) ^ 2)
    (hlogTwelve : Real.log (X : ℝ) ^ 12 ≤ (y : ℝ)) :
    mrWeightedCofactorContourBudget C (mrCofactorAverageEnvelope N X)
        y X (mrCofactorDyadicHeight X) (Real.log (y : ℝ))⁻¹ (Real.log (X : ℝ) ^ 2) ≤
      mrCofactorContourScalarConstant *
        (10 * gsA10SmallPowerSourceRowBound C * gsA10PrimeLambdaHarmonicLogConstant * Real.log (X : ℝ) +
          gsA10SourceHPPRectangleBound / Real.log (X : ℝ)) / (N * Real.log (y : ℝ)) := by
  let L := Real.log (X : ℝ)
  let R := 10 * gsA10SmallPowerSourceRowBound C
  let H := gsA10PrimeLambdaHarmonicLogConstant
  let B := gsA10SourceHPPRectangleBound
  have hL : 0 < L := zero_lt_one.trans_le hlogX
  have hlogy : 0 < Real.log (y : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hrow0 : 0 ≤ R := mul_nonneg (by norm_num) (gsA10SmallPowerSourceRowBound_nonneg hC)
  have hH0 : 0 ≤ H := gsA10PrimeLambdaHarmonicLogConstant_nonneg
  have hB0 : 0 ≤ B := gsA10SourceHPPRectangleBound_nonneg
  have hlogFour : L ^ 4 ≤ (y : ℝ) :=
    (pow_le_pow_right₀ hlogX (by norm_num : 4 ≤ 12)).trans hlogTwelve
  have hrow := mrCofactor_weightedRow_le hC (show 0 < y by omega) hX hlogFour
  have hH := gsA10PrimeLambdaHarmonicBudget_le_log (show 2 ≤ X by omega)
  have hHnonneg : 0 ≤ gsA10PrimeLambdaHarmonicBudget X := by
    unfold gsA10PrimeLambdaHarmonicBudget
    positivity
  have hpp := mrCofactor_uniformHigherPowerFactor_le
    (show 2 ≤ X by omega) hy hlogX hprime hlogSquare hlogTwelve
  have hinner : gsA10PrimeSourceWeightedRowFactor C y X (mrCofactorDyadicHeight X) *
        gsA10PrimeLambdaHarmonicBudget X + 4 * L ^ 2 * mrWeightedCofactorUniformSplitError y X ≤
      R * H * L + B / L := by
    have hmain := mul_le_mul hrow hH hHnonneg hrow0
    calc
      _ ≤ R * (H * L) + B / L := add_le_add hmain hpp
      _ = _ := by ring
  have hM := mrCofactorAverageEnvelope_le_log hN (show 1 < X by omega) hlogX
  have hMhalf : mrCofactorAverageEnvelope N X / 2 ≤
      mrCofactorAverageEnvelopeConstant * L / N := by
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).2
    calc
      _ ≤ 2 * mrCofactorAverageEnvelopeConstant * Real.log (X : ℝ) / N := hM
      _ = _ := by dsimp only [L]; ring
  have hM0 : 0 ≤ mrCofactorAverageEnvelope N X / 2 := by
    unfold mrCofactorAverageEnvelope mrCofactorEulerBase
    positivity
  have hCav0 : 0 ≤ mrCofactorAverageEnvelopeConstant := by
    unfold mrCofactorAverageEnvelopeConstant mrCofactorEulerBaseConstant
    positivity
  unfold mrWeightedCofactorContourBudget mrWeightedCofactorContourCoefficient
  calc
    _ ≤ (4 * (2 * Real.pi)⁻¹ * Real.exp 1 * (Real.log (y : ℝ))⁻¹ / L) *
        (mrCofactorAverageEnvelopeConstant * L / N * (R * H * L + B / L)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact (mul_le_mul_of_nonneg_left hinner hM0).trans
        (mul_le_mul_of_nonneg_right hMhalf (by positivity))
    _ = _ := by
      dsimp only [mrCofactorContourScalarConstant, R, H, B, L]
      field_simp

theorem mrCofactor_contourBudget_le_inverse_nonpretentious {C delta : ℝ}
    (hC : 1 ≤ C) (hdelta : 0 < delta) {N y X : ℕ}
    (hN : 0 < N) (hX : 4 ≤ X) (hy : 3 ≤ y) (hlogX : 1 ≤ Real.log (X : ℝ))
    (hprime : PrimeEstimates.primeReciprocals X ≤ Real.log (X : ℝ))
    (hlogSquare : 4 * Real.log (X : ℝ) ≤ Real.log (y : ℝ) ^ 2)
    (hlogTwelve : Real.log (X : ℝ) ^ 12 ≤ (y : ℝ))
    (hcutoff : delta * Real.log (X : ℝ) ≤ Real.log (y : ℝ)) :
    mrWeightedCofactorContourBudget C (mrCofactorAverageEnvelope N X)
        y X (mrCofactorDyadicHeight X) (Real.log (y : ℝ))⁻¹ (Real.log (X : ℝ) ^ 2) ≤
      mrCofactorContourMeanConstant C / (N * delta) := by
  have hL : 0 < Real.log (X : ℝ) := zero_lt_one.trans_le hlogX
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hlogy : 0 < Real.log (y : ℝ) := (mul_pos hdelta hL).trans_le hcutoff
  have hB := gsA10SourceHPPRectangleBound_nonneg
  have hR := gsA10SmallPowerSourceRowBound_nonneg hC
  have hH := gsA10PrimeLambdaHarmonicLogConstant_nonneg
  have hBterm : gsA10SourceHPPRectangleBound / Real.log (X : ℝ) ≤
      gsA10SourceHPPRectangleBound * Real.log (X : ℝ) := by
    apply (div_le_iff₀ hL).2
    have hsq : (1 : ℝ) ≤ Real.log (X : ℝ) ^ 2 := one_le_pow₀ hlogX
    nlinarith [mul_le_mul_of_nonneg_left hsq hB]
  apply (mrCofactor_contourBudget_le_scalar hC hN hX hy hlogX hprime hlogSquare hlogTwelve).trans
  calc
    _ ≤ mrCofactorContourScalarConstant *
        ((10 * gsA10SmallPowerSourceRowBound C * gsA10PrimeLambdaHarmonicLogConstant +
          gsA10SourceHPPRectangleBound) * Real.log (X : ℝ)) / (N * Real.log (y : ℝ)) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_left _ mrCofactorContourScalarConstant_nonneg
      nlinarith
    _ ≤ mrCofactorContourScalarConstant *
        ((10 * gsA10SmallPowerSourceRowBound C * gsA10PrimeLambdaHarmonicLogConstant +
          gsA10SourceHPPRectangleBound) * Real.log (X : ℝ)) / (N * (delta * Real.log (X : ℝ))) := by
      apply div_le_div_of_nonneg_left
      · exact mul_nonneg mrCofactorContourScalarConstant_nonneg (by positivity)
      · positivity
      · exact mul_le_mul_of_nonneg_left hcutoff (Nat.cast_nonneg N)
    _ = _ := by
      unfold mrCofactorContourMeanConstant
      field_simp

end

end Erdos67b
