import ErdosProblems.Erdos67b.MRCofactorWeightedPrime
import ErdosProblems.Erdos67b.MRGSA10FixedHighVerticalContour

/-!
# Actual Mangoldt windows with the Perron denominator retained

The prime product uses weighted energies. Only the explicit higher-power
remainder uses the elementary reciprocal-denominator bound of two.
-/

open scoped LSeries.notation
open Complex MeasureTheory Set

namespace Erdos67b

open MRHalaszBands EulerResidue

noncomputable section

theorem mrExists_weightedLambda_fixedHigh_pair_le :
    ∃ C : ℝ, ∃ Y : ℕ, 1 ≤ C ∧
      ∀ {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
        (_hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
        (y X : ℕ) (beta sigma T M : ℝ) (K : ℕ) (F : ℝ → ℂ),
        Y ≤ y → 2 ≤ X → 0 ≤ beta → 1 / 2 ≤ sigma → 0 ≤ T →
        T ≤ (((2 : ℕ) ^ K : ℕ) : ℝ) → 0 ≤ M → Continuous F →
        (∀ t, |t| ≤ T → ‖F t‖ ≤ M) →
        ‖∫ t in -T..T,
          F t * LSeries (gsA10LambdaWindow (gsA9HighGeneralizedMangoldt hmul y) y X)
              (((taoExponent X - 2 * beta : ℝ) : ℂ) + I * (t : ℂ)) *
            LSeries (gsA10LambdaWindow (gsA9HighGeneralizedMangoldt hmul y) y X)
              ((taoExponent X : ℂ) + I * (t : ℂ)) /
            ((sigma : ℂ) + I * (t : ℂ))‖ ≤
          M * (gsA10PrimeSourceWeightedRowFactor C y X K *
              (((X / y : ℕ) : ℝ) ^ (2 * beta) * gsA10PrimeLambdaHarmonicBudget X) +
            4 * T * gsA10LambdaVerticalSplitError y X (taoExponent X - 2 * beta) (taoExponent X)) := by
  obtain ⟨C, Y, hC, henergy⟩ := mrExists_weightedPrime_fixedHigh_pair_le
  refine ⟨C, Y, hC, ?_⟩
  intro f hmul hbound y X beta sigma T M K F hY hX hbeta hsigma hT hTK hM hF hFbound
  let s : ℝ → ℂ := fun t ↦ (sigma : ℂ) + I * (t : ℂ)
  let W := gsA10LambdaWindow (gsA9HighGeneralizedMangoldt hmul y) y X
  let A₁ : ℝ → ℂ := fun t ↦ LSeries W (((taoExponent X - 2 * beta : ℝ) : ℂ) + I * (t : ℂ))
  let A₂ : ℝ → ℂ := fun t ↦ LSeries W ((taoExponent X : ℂ) + I * (t : ℂ))
  let P₁ := gsA10PrimeLambdaPolynomial hmul y X (taoExponent X - 2 * beta)
  let P₂ := gsA10PrimeLambdaPolynomial hmul y X (taoExponent X)
  let E := gsA10LambdaVerticalSplitError y X (taoExponent X - 2 * beta) (taoExponent X)
  let R := gsA10PrimeSourceWeightedRowFactor C y X K *
    (((X / y : ℕ) : ℝ) ^ (2 * beta) * gsA10PrimeLambdaHarmonicBudget X)
  have hP₁ : Continuous P₁ := continuous_gsA10PrimeLambdaPolynomial hmul y X _
  have hP₂ : Continuous P₂ := continuous_gsA10PrimeLambdaPolynomial hmul y X _
  have hA₁ : Continuous A₁ := continuous_LSeries_gsA10LambdaWindow hmul y X _
  have hA₂ : Continuous A₂ := continuous_LSeries_gsA10LambdaWindow hmul y X _
  have hs : Continuous s := by dsimp only [s]; fun_prop
  have hsNorm : ∀ t, (1 / 2 : ℝ) ≤ ‖s t‖ := by
    intro t
    have hre : (s t).re = sigma := by simp [s]
    have h := abs_re_le_norm (s t)
    rw [hre, abs_of_nonneg (by linarith : 0 ≤ sigma)] at h
    exact hsigma.trans h
  have hsNe : ∀ t, s t ≠ 0 := fun t ↦ norm_pos_iff.mp (lt_of_lt_of_le (by norm_num) (hsNorm t))
  have hdiv : Continuous (fun t ↦ F t / s t) := hF.div hs hsNe
  have hdivBound : ∀ t, |t| ≤ T → ‖F t / s t‖ ≤ 2 * M := by
    intro t ht
    rw [norm_div]
    calc
      _ ≤ M / ‖s t‖ := div_le_div_of_nonneg_right (hFbound t ht) (norm_nonneg _)
      _ ≤ M / (1 / 2 : ℝ) := div_le_div_of_nonneg_left hM (by norm_num) (hsNorm t)
      _ = _ := by ring
  have hprime : ‖∫ t in -T..T, F t * P₁ (-t) * P₂ (-t) / s t‖ ≤ M * R := by
    have hbase := mrNorm_intervalIntegral_triple_div_vertical_le_weightedEnergy
      F (fun t ↦ P₁ (-t)) (fun t ↦ P₂ (-t)) hF
      (hP₁.comp continuous_neg) (hP₂.comp continuous_neg) hsigma hT hM hFbound
    rw [mrWeightedVerticalEnergy_comp_neg, mrWeightedVerticalEnergy_comp_neg] at hbase
    have hp := henergy hmul hbound y X beta sigma T K hY hX hbeta hsigma hT hTK
    exact hbase.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hp hM)
  have herr : ‖∫ t in -T..T, (F t / s t) * (A₁ t * A₂ t - P₁ (-t) * P₂ (-t))‖ ≤
      4 * T * M * E := by
    have hraw := norm_intervalIntegral_mul_LambdaWindowProduct_sub_primeProduct_le
      hmul hbound (y := y) hX (taoExponent X - 2 * beta) (taoExponent X) hT
      (mul_nonneg (by norm_num) hM) (fun t ↦ F t / s t) hdivBound
    convert hraw using 1
    ring
  have hPint : IntervalIntegrable (fun t ↦ F t * P₁ (-t) * P₂ (-t) / s t) volume (-T) T :=
    (((hF.mul (hP₁.comp continuous_neg)).mul (hP₂.comp continuous_neg)).div hs hsNe).intervalIntegrable _ _
  have hEint : IntervalIntegrable (fun t ↦ (F t / s t) * (A₁ t * A₂ t - P₁ (-t) * P₂ (-t)))
      volume (-T) T :=
    (hdiv.mul ((hA₁.mul hA₂).sub ((hP₁.comp continuous_neg).mul
      (hP₂.comp continuous_neg)))).intervalIntegrable _ _
  have hdecomp : (∫ t in -T..T, F t * A₁ t * A₂ t / s t) =
      (∫ t in -T..T, F t * P₁ (-t) * P₂ (-t) / s t) +
        ∫ t in -T..T, (F t / s t) * (A₁ t * A₂ t - P₁ (-t) * P₂ (-t)) := by
    rw [← intervalIntegral.integral_add hPint hEint]
    apply intervalIntegral.integral_congr
    intro t _
    ring
  change ‖∫ t in -T..T, F t * A₁ t * A₂ t / s t‖ ≤ M * (R + 4 * T * E)
  rw [hdecomp]
  calc
    _ ≤ M * R + 4 * T * M * E := (norm_add_le _ _).trans (add_le_add hprime herr)
    _ = _ := by ring

end

end Erdos67b
