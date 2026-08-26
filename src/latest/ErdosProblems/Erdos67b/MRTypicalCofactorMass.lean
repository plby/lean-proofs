import ErdosProblems.Erdos67b.MRTypicalCofactorProjection
import ErdosProblems.Erdos67b.MRGSA10CoefficientMassSourceScalar
import ErdosProblems.Erdos67b.MRGSA9SmallPrimeRestore

/-!
# One-pole absolute mass for the actual typical cofactor

The low coefficient is bounded by the positive smooth-number coefficient.
Its Euler majorant is shifted and recombined with the positive high factor
before the zeta bound. The two finite Lambda windows retain their ordinary
higher-prime-power correction.
-/

open scoped BigOperators Classical LSeries.notation ComplexOrder
open Finset

namespace Erdos67b

open MRHalaszBands EulerResidue BoundedGaps.Maynard

noncomputable section

theorem mrLSeries_low_eq_smallPrime_mul_delete
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1) {y : ℕ} (hy : 23 ≤ y)
    {s : ℂ} (hs : 0 < s.re) :
    LSeries (gsA9Low f y) s = gsA9SmallPrimeEulerProduct f s *
      LSeries (gsA9Low (gsDeletePrimeBand f gsA9SmallPrime) y) s := by
  rw [LSeries_gsA9Low_eq_finiteEulerProduct_of_pos_re hmul hbound y hs,
    LSeries_gsA9Low_eq_finiteEulerProduct_of_pos_re
      (gsDeletePrimeBand_isMultiplicativeOnPositiveNat hmul gsA9SmallPrime)
      (fun n hn ↦ norm_gsDeletePrimeBand_le_one hbound gsA9SmallPrime hn) y hs]
  have hprod := prod_filter_eq_smallPrimeEulerProduct_mul_delete hmul (fun _ ↦ True)
    hy (fun _ _ ↦ trivial) s
  simpa only [Finset.filter_true] using hprod

theorem mrNorm_positiveLow_mul_positiveHigh_le
    {y : ℕ} (hy : 23 ≤ y) {sigmaLow sigmaHigh : ℝ}
    (hhalf : 1 / 2 ≤ sigmaLow) (hhigh : 1 < sigmaHigh)
    (hle : sigmaLow ≤ sigmaHigh)
    (hwide : 1 - 3 / Real.log (y : ℝ) ≤ sigmaLow)
    (hgap : sigmaHigh - sigmaLow ≤ 3 / Real.log (y : ℝ)) :
    ‖LSeries (gsA9Low (fun _ : ℕ ↦ (1 : ℂ)) y) (sigmaLow : ℂ)‖ *
      ‖LSeries (gsA9High (fun _ : ℕ ↦ (1 : ℂ)) y) (sigmaHigh : ℂ)‖ ≤
      gsA10SourceCoefficientMassConstant * (1 + (sigmaHigh - 1)⁻¹) := by
  let one : ℕ → ℂ := fun _ ↦ 1
  let g := gsDeletePrimeBand one gsA9SmallPrime
  have hone : IsMultiplicativeOnPositiveNat one := ⟨rfl, fun _ _ _ _ _ ↦ by simp [one]⟩
  have hbound : ∀ n, 0 < n → ‖one n‖ ≤ 1 := fun _ _ ↦ by simp [one]
  have hshift := mrNorm_maskedLow_mul_high_shift_le hone hbound (fun p ↦ 23 ≤ p)
    (by omega : 2 ≤ y) (fun p hp ↦ by omega) (fun _ _ hp ↦ hp)
    hhalf hle hwide hgap hhigh (t := 0)
  rw [← mrDeleteSmallPrimes_eq_largePrimeBand] at hshift
  have hshift' : ‖LSeries (gsA9Low g y) (sigmaLow : ℂ)‖ *
      ‖LSeries (gsA9High one y) (sigmaHigh : ℂ)‖ ≤
      Real.exp (6 * gsA9WideSourceShiftConstant) * ‖LSeries g (sigmaHigh : ℂ)‖ := by
    simpa only [Complex.ofReal_zero, mul_zero, add_zero, norm_mul] using hshift
  have hsmall : ‖gsA9SmallPrimeEulerProduct one (sigmaLow : ℂ)‖ ≤ gsA9SmallPrimeEulerBound := by
    simpa only [Complex.ofReal_zero, mul_zero, add_zero] using
      norm_gsA9SmallPrimeEulerProduct_le hbound (t := 0) hhalf
  have hL : ‖LSeries g (sigmaHigh : ℂ)‖ ≤ 1 + (sigmaHigh - 1)⁻¹ := by
    have hζ := norm_LSeries_le_norm_riemannZeta_real_of_bounded
      (fun n hn ↦ norm_gsDeletePrimeBand_le_one hbound gsA9SmallPrime hn)
      (sigma := sigmaHigh) (t := 0) hhigh
    have hζ' := norm_riemannZeta_real_le_one_add_inv (sigma := sigmaHigh - 1) (by linarith)
    have hline : 1 + (sigmaHigh - 1) = sigmaHigh := by ring
    rw [hline] at hζ'
    have hζ'' : ‖LSeries g (sigmaHigh : ℂ)‖ ≤ ‖riemannZeta (sigmaHigh : ℂ)‖ := by
      simpa only [Complex.ofReal_zero, mul_zero, add_zero] using hζ
    exact hζ''.trans hζ'
  change ‖LSeries (gsA9Low one y) (sigmaLow : ℂ)‖ * _ ≤ _
  rw [mrLSeries_low_eq_smallPrime_mul_delete hone hbound hy (by simpa using (show 0 < sigmaLow by linarith)),
    norm_mul, mul_assoc]
  calc
    _ ≤ gsA9SmallPrimeEulerBound *
        (Real.exp (6 * gsA9WideSourceShiftConstant) * ‖LSeries g (sigmaHigh : ℂ)‖) :=
      mul_le_mul hsmall hshift' (mul_nonneg (norm_nonneg _) (norm_nonneg _))
        ((norm_nonneg _).trans hsmall)
    _ = gsA10SourceCoefficientMassConstant * ‖LSeries g (sigmaHigh : ℂ)‖ := by
      unfold gsA10SourceCoefficientMassConstant
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hL gsA10SourceCoefficientMassConstant_nonneg

theorem mrCofactorLowCoefficientMass_le_positive {ι : Type*}
    (A : Finset ℕ) (J : Finset ι) (B : ι → Finset ℕ)
    {f : ℕ → ℂ} (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (y : ℕ) {sigma : ℝ} (hsigma : 0 < sigma) :
    dirichletPerronCoefficientMass (mrTypicalCofactorLowArithmetic A J B f y) sigma ≤
      ‖LSeries (gsA9Low (fun _ : ℕ ↦ (1 : ℂ)) y) (sigma : ℂ)‖ := by
  have hsumA : LSeriesSummable (gsA9Low (fun _ : ℕ ↦ (1 : ℂ)) y) (sigma : ℂ) :=
    mrPrimeBandCoefficient_LSeriesSummable_of_bounded_pos_re (fun _ _ ↦ by simp)
      (fun p ↦ p ≤ y) y (fun _ hp ↦ hp) (by simpa using hsigma)
  have hsumB := mrTypicalCofactorLowArithmetic_LSeriesSummable_of_pos_re A J B hbound y
    (s := (sigma : ℂ)) (by simpa using hsigma)
  apply dirichletPerronCoefficientMass_le_norm_LSeries_of_major hsumA hsumB
  · intro n
    unfold gsA9Low primeBandCoefficient
    split_ifs <;> simp
  · intro n
    by_cases hn : n = 0
    · subst n
      simp [gsA9Low, primeBandCoefficient, PrimeSupported]
    · by_cases hsupp : PrimeSupported (fun p ↦ p ≤ y) n
      · simpa [mrTypicalCofactorLowArithmetic, toArithmeticFunction, gsA9Low,
          primeBandCoefficient, hn, hsupp] using
          mrIndexedTypicalCofactorCoefficient_norm_le_one A J B hbound (Nat.pos_of_ne_zero hn)
      · simp [mrTypicalCofactorLowArithmetic, toArithmeticFunction, gsA9Low,
          primeBandCoefficient, hn, hsupp]

theorem mrCofactorLowHighCoefficientMass_le {ι : Type*}
    (A : Finset ℕ) (J : Finset ι) (B : ι → Finset ℕ)
    {f : ℕ → ℂ} (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {y : ℕ} (hy : 23 ≤ y) {sigmaLow sigmaHigh : ℝ}
    (hhalf : 1 / 2 ≤ sigmaLow) (hhigh : 1 < sigmaHigh)
    (hle : sigmaLow ≤ sigmaHigh)
    (hwide : 1 - 3 / Real.log (y : ℝ) ≤ sigmaLow)
    (hgap : sigmaHigh - sigmaLow ≤ 3 / Real.log (y : ℝ)) :
    dirichletPerronCoefficientMass (mrTypicalCofactorLowArithmetic A J B f y) sigmaLow *
      dirichletPerronCoefficientMass (gsA9HighArithmetic f y) sigmaHigh ≤
      gsA10SourceCoefficientMassConstant * (1 + (sigmaHigh - 1)⁻¹) := by
  apply (mul_le_mul (mrCofactorLowCoefficientMass_le_positive A J B hbound y (by linarith))
    (dirichletPerronCoefficientMass_gsA9HighArithmetic_le_positive hbound y hhigh)
    (tsum_nonneg (fun _ ↦ norm_nonneg _)) (norm_nonneg _)).trans
  exact mrNorm_positiveLow_mul_positiveHigh_le hy hhalf hhigh hle hwide hgap

theorem mrCofactorLowHighCoefficientMass_fixedTao_le {ι : Type*}
    (A : Finset ℕ) (J : Finset ι) (B : ι → Finset ℕ)
    {f : ℕ → ℂ} (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {y X : ℕ} (hy : 23 ≤ y) (hX : 1 < X)
    {alpha beta : ℝ} (hlogy : 6 ≤ Real.log (y : ℝ))
    (ha0 : 0 ≤ alpha) (ha : alpha ≤ (Real.log (y : ℝ))⁻¹)
    (hb0 : 0 ≤ beta) (hb : beta ≤ (Real.log (y : ℝ))⁻¹) :
    dirichletPerronCoefficientMass (mrTypicalCofactorLowArithmetic A J B f y)
        (taoExponent X - alpha - 2 * beta) *
      dirichletPerronCoefficientMass (gsA9HighArithmetic f y) (taoExponent X) ≤
      gsA10SourceCoefficientMassConstant * (1 + Real.log (X : ℝ)) := by
  have hc := one_lt_taoExponent hX
  have hinv : (Real.log (y : ℝ))⁻¹ ≤ 1 / 6 := by
    simpa only [one_div] using inv_anti₀ (by norm_num : (0 : ℝ) < 6) hlogy
  have hh := mrCofactorLowHighCoefficientMass_le A J B hbound hy
    (sigmaLow := taoExponent X - alpha - 2 * beta) (sigmaHigh := taoExponent X)
    (by linarith) hc (by linarith) (by simp only [div_eq_mul_inv]; linarith)
    (by simp only [div_eq_mul_inv]; linarith)
  simpa only [taoExponent, add_sub_cancel_left, inv_inv] using hh

theorem mrCofactorTailoredCoefficientMass_fixedTao_le {ι : Type*}
    (A : Finset ℕ) (J : Finset ι) (B : ι → Finset ℕ)
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {y X : ℕ} (hy : 23 ≤ y) (hX : 1 < X)
    {alpha beta : ℝ} (hlogy : 6 ≤ Real.log (y : ℝ))
    (ha0 : 0 ≤ alpha) (ha : alpha ≤ (Real.log (y : ℝ))⁻¹)
    (hb0 : 0 ≤ beta) (hb : beta ≤ (Real.log (y : ℝ))⁻¹) :
    dirichletPerronCoefficientMass (mrTypicalCofactorTailoredCoefficient A J B f hmul y X alpha beta)
        (taoExponent X - alpha - 2 * beta) ≤
      (gsA10SourceCoefficientMassConstant * (1 + Real.log (X : ℝ))) *
        ((gsA10OrdinaryLambdaWindowMassBase y X) ^ 2 *
          (X : ℝ) ^ (1 - min (taoExponent X - 2 * beta) 1)) := by
  have hc := one_lt_taoExponent hX
  have hinv : (Real.log (y : ℝ))⁻¹ ≤ 1 / 6 := by
    simpa only [one_div] using inv_anti₀ (by norm_num : (0 : ℝ) < 6) hlogy
  have hlow := mrTypicalCofactorLowArithmetic_LSeriesSummable_of_pos_re A J B hbound y
    (s := ((taoExponent X - alpha - 2 * beta : ℝ) : ℂ)) (by
      simp only [Complex.ofReal_re]
      linarith)
  have hhigh := gsA9HighArithmetic_LSeriesSummable hbound y
    (s := (taoExponent X : ℂ)) (by simpa using hc)
  have hfour := dirichletPerronCoefficientMass_gsA10Tailored_ordinary_fixedHigh_le hmul hbound
    (mrTypicalCofactorLowArithmetic A J B f y) (gsA9HighArithmetic f y)
    (by omega) hlogy hb0 hb hlow hhigh
  exact hfour.trans (mul_le_mul_of_nonneg_right
    (mrCofactorLowHighCoefficientMass_fixedTao_le A J B hbound hy hX hlogy ha0 ha hb0 hb)
    (by positivity))

end

end Erdos67b
