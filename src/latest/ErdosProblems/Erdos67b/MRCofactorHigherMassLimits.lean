import ErdosProblems.Erdos67b.MRCofactorProjectionScales
import ErdosProblems.Erdos67b.MRGSA10RestoredPerronScalar
import ErdosProblems.Erdos67b.MRGSA10PrimeLambdaBetaDiagonalScalar

/-! # Vanishing higher-prime-power masses at the power cutoff -/

open Filter
open scoped Topology

namespace Erdos67b

open MRHalaszBands

noncomputable section

theorem mrCofactor_higherMass_le_log_sq {y X Z : ℕ} (hy : 3 ≤ y) (hX : 2 ≤ X)
    (hZ : 2 ≤ Z) (hZX : Z ≤ 2 * X)
    (hprime : PrimeEstimates.primeReciprocals (2 * X) ≤ Real.log (X : ℝ)) :
    gsA10HigherPrimePowerGeometricMass y Z ≤ 72 * Real.log (X : ℝ) ^ 2 / y := by
  have hL : 0 ≤ Real.log (X : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ X by omega))
  have hZpos : (0 : ℝ) < Z := by positivity
  have hlog : Real.log (Z : ℝ) ≤ 2 * Real.log (X : ℝ) :=
    (Real.log_le_log hZpos (by exact_mod_cast hZX)).trans (mrCofactor_log_two_mul_le hX)
  have hR := (mrPrimeReciprocals_mono hZX).trans hprime
  calc
    _ ≤ 12 * Real.log (Z : ℝ) / y * PrimeEstimates.primeReciprocals Z :=
      gsA10HigherPrimePowerGeometricMass_le hy
    _ ≤ (12 * (2 * Real.log (X : ℝ)) / y) * Real.log (X : ℝ) := by
      apply mul_le_mul
      · exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hlog (by norm_num)) (Nat.cast_nonneg y)
      · exact hR
      · exact PrimeEstimates.primeReciprocals_nonneg Z
      · positivity
    _ = 24 * (Real.log (X : ℝ) ^ 2 / y) := by ring
    _ ≤ 72 * (Real.log (X : ℝ) ^ 2 / y) := by
      gcongr
      norm_num
    _ = _ := by ring

theorem mrCofactor_harmonic_mul_higherMass_le_log_cube {y X Z : ℕ}
    (hy : 3 ≤ y) (hX : 2 ≤ X) (hZ : 2 ≤ Z) (hZX : Z ≤ 2 * X)
    (hprime : PrimeEstimates.primeReciprocals (2 * X) ≤ Real.log (X : ℝ)) :
    gsA10PrimeLambdaHarmonicBudget Z * gsA10HigherPrimePowerGeometricMass y Z ≤
      144 * gsA10PrimeLambdaHarmonicLogConstant * Real.log (X : ℝ) ^ 3 / y := by
  have hL : 0 ≤ Real.log (X : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ X by omega))
  have hC := gsA10PrimeLambdaHarmonicLogConstant_nonneg
  have hlog : Real.log (Z : ℝ) ≤ 2 * Real.log (X : ℝ) :=
    (Real.log_le_log (by positivity : (0 : ℝ) < Z) (by exact_mod_cast hZX)).trans
      (mrCofactor_log_two_mul_le hX)
  have hH : gsA10PrimeLambdaHarmonicBudget Z ≤
      gsA10PrimeLambdaHarmonicLogConstant * (2 * Real.log (X : ℝ)) :=
    (gsA10PrimeLambdaHarmonicBudget_le_log hZ).trans (mul_le_mul_of_nonneg_left hlog hC)
  calc
    _ ≤ (gsA10PrimeLambdaHarmonicLogConstant * (2 * Real.log (X : ℝ))) *
        (72 * Real.log (X : ℝ) ^ 2 / y) :=
      mul_le_mul hH (mrCofactor_higherMass_le_log_sq hy hX hZ hZX hprime)
        (gsA10HigherPrimePowerGeometricMass_nonneg_source y Z) (by positivity)
    _ = _ := by ring

theorem mrTendsto_higherMass_at_cofactorPowerCutoff {delta : ℝ} (hdelta : 0 < delta)
    (Z : ℕ → ℕ) (hZ : ∀ᶠ X : ℕ in atTop, 2 ≤ Z X ∧ Z X ≤ 2 * X) :
    Tendsto (fun X : ℕ ↦ gsA10HigherPrimePowerGeometricMass (mrCofactorPowerCutoff delta X) (Z X))
      atTop (𝓝 0) := by
  apply squeeze_zero'
  · exact Eventually.of_forall (fun X ↦ gsA10HigherPrimePowerGeometricMass_nonneg_source _ _)
  · filter_upwards [hZ, eventually_ge_atTop 2, mrEventually_primeReciprocals_two_mul_le_log,
      (mrTendsto_cofactorPowerCutoff hdelta).eventually (eventually_ge_atTop 3)] with X hZ hX hprime hy
    exact mrCofactor_higherMass_le_log_sq hy hX hZ.1 hZ.2 hprime
  · simpa only [mul_div_assoc, mul_zero] using (mrTendsto_log_pow_div_cofactorPowerCutoff hdelta 2).const_mul 72

theorem mrTendsto_harmonic_mul_higherMass_at_cofactorPowerCutoff {delta : ℝ} (hdelta : 0 < delta)
    (Z : ℕ → ℕ) (hZ : ∀ᶠ X : ℕ in atTop, 2 ≤ Z X ∧ Z X ≤ 2 * X) :
    Tendsto (fun X : ℕ ↦ gsA10PrimeLambdaHarmonicBudget (Z X) *
      gsA10HigherPrimePowerGeometricMass (mrCofactorPowerCutoff delta X) (Z X)) atTop (𝓝 0) := by
  apply squeeze_zero'
  · apply Eventually.of_forall
    intro X
    have hH : 0 ≤ gsA10PrimeLambdaHarmonicBudget (Z X) := by
      unfold gsA10PrimeLambdaHarmonicBudget
      positivity
    exact mul_nonneg hH (gsA10HigherPrimePowerGeometricMass_nonneg_source _ _)
  · filter_upwards [hZ, eventually_ge_atTop 2, mrEventually_primeReciprocals_two_mul_le_log,
      (mrTendsto_cofactorPowerCutoff hdelta).eventually (eventually_ge_atTop 3)] with X hZ hX hprime hy
    exact mrCofactor_harmonic_mul_higherMass_le_log_cube hy hX hZ.1 hZ.2 hprime
  · simpa only [mul_div_assoc, mul_zero] using
      (mrTendsto_log_pow_div_cofactorPowerCutoff hdelta 3).const_mul (144 * gsA10PrimeLambdaHarmonicLogConstant)

end

end Erdos67b
