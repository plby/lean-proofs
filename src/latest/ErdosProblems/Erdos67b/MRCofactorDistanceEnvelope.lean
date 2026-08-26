import ErdosProblems.Erdos67b.MRShiftedMaskSum
import ErdosProblems.Erdos67b.MRCofactorScaledDistance

/-!
# Cofactor envelope independent of the selected-prime mass

The scaling parameter is retained in the distance exponential until the
actual denominator average is performed. Only an inverse-distance cost
remains, with all positive-line convergence already proved.
-/

open scoped BigOperators Classical LSeries.notation
open Complex Set MeasureTheory

namespace Erdos67b

open MRHalaszBands MRHalaszEuler EulerResidue EulerQuantitative BoundedGaps.Maynard

noncomputable section

def mrCofactorEulerBase (X : ℕ) : ℝ :=
  Real.exp (6 * gsA9WideSourceShiftConstant +
    Real.log (riemannZeta (taoExponent X : ℂ)).re +
    3 * primeQuadraticConstant + mrMaskProductSeries)

def mrCofactorAverageEnvelope (N X : ℕ) : ℝ :=
  mrCofactorEulerBase X * ((Real.exp (-1) / 16) * ((N : ℝ) / 2))⁻¹

theorem mrNorm_scaledTypicalLow_mul_high_le_scaleDistance
    (A : Finset ℕ) (hA : ∀ p ∈ A, p.Prime)
    (J : Finset ℕ) (B : ℕ → Finset ℕ) {X y : ℕ} (hX : 1 < X) (hy : 23 ≤ y)
    (hJ : ∀ j ∈ J, 1 ≤ j) (hB : ∀ j ∈ J, B j ⊆ primesUpTo X)
    (hdisj : Set.PairwiseDisjoint (↑J : Set ℕ) B)
    (hsmall : ∀ j ∈ J, ∀ p ∈ B j, Real.log (p : ℝ) ≤ Real.log (X : ℝ) / 16)
    (hmass : ∀ j ∈ J, 2 * Real.log (j : ℝ) ≤ ∑ p ∈ B j, 1 / (p : ℝ))
    (hAy : ∀ p ∈ A, p ≤ y) (hBy : ∀ j ∈ J, ∀ p ∈ B j, p ≤ y)
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (hfixed : primeBandCoefficient f (fun p ↦ 23 ≤ p) = f)
    {sigmaLow u : ℝ} (hhalf : 1 / 2 ≤ sigmaLow)
    (hle : sigmaLow ≤ taoExponent X)
    (hsigma : 1 - 3 / Real.log (y : ℝ) ≤ sigmaLow)
    (hgap : taoExponent X - sigmaLow ≤ 3 / Real.log (y : ℝ))
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (t : ℝ) :
    ‖LSeries (gsA9Low (mrIndexedTypicalCoefficient J B (mrPrimeScaledCoefficient A f u)) y)
          ((sigmaLow : ℂ) + Complex.I * (t : ℂ)) *
        LSeries (gsA9High f y) (halaszPoint X t)‖ ≤
      mrCofactorEulerBase X *
        Real.exp (-(Real.exp (-1) / 16) * u * pretentiousDistSq f (archimedeanTwist t) X) := by
  let g := mrPrimeScaledCoefficient A f u
  have hgmul := mrPrimeScaledCoefficient_isMultiplicative hA hmul u
  have hgbound : ∀ n, 0 < n → ‖g n‖ ≤ 1 :=
    fun n hn ↦ norm_mrPrimeScaledCoefficient_le_one hbound hu0 hu1 hn
  have hgf : primeBandCoefficient g (fun p ↦ 23 ≤ p) = g :=
    mrPrimeScaled_largePrimeSupported A hfixed u
  have hhigh : gsA9High g y = gsA9High f y :=
    mrHigh_primeScaledCoefficient_eq A hA f y hAy u
  have hsLow : 0 < ((sigmaLow : ℂ) + Complex.I * (t : ℂ)).re := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.I_im, Complex.ofReal_im, zero_mul, one_mul, sub_zero, add_zero]
    linarith
  have hfirst := mrNorm_LSeries_low_indexedTypical_mul_le_mask_sum J B
    (fun j hj p hp ↦ (mem_primesUpTo.mp (hB j hj hp)).1) hgbound y hsLow
    (LSeries (gsA9High f y) (halaszPoint X t))
  have hmask (S : Finset ℕ) (hS : S ∈ J.powerset) :
      ‖LSeries (gsA9Low (primeBandCoefficient g (fun p ↦ p ∉ S.biUnion B)) y)
          ((sigmaLow : ℂ) + Complex.I * (t : ℂ)) *
        LSeries (gsA9High f y) (halaszPoint X t)‖ ≤
      Real.exp (6 * gsA9WideSourceShiftConstant) *
        ‖LSeries (primeBandCoefficient g (fun p ↦ p ∉ S.biUnion B)) (halaszPoint X t)‖ := by
    have hsmallS : ∀ p, ¬ (p ∉ S.biUnion B) → p ≤ y := by
      intro p hp
      obtain ⟨j, hj, hpj⟩ := Finset.mem_biUnion.mp (not_not.mp hp)
      exact hBy j (Finset.mem_powerset.mp hS hj) p hpj
    have hh := mrNorm_maskedLow_mul_high_shift_le_of_largePrimeSupport hgmul hgbound hgf
      (fun p ↦ p ∉ S.biUnion B) hy hsmallS hhalf hle hsigma hgap (one_lt_taoExponent hX) (t := t)
    rw [hhigh] at hh
    exact hh
  have hsum := mrSum_norm_masked_LSeries_le J B hX hJ hB hdisj hsmall hmass hgmul hgbound t
  have hdist := mrPretentiousDistSq_scaled_ge_mul hA hu1 X
    (fun p hp ↦ hbound p hp.pos) (fun p hp ↦ (norm_archimedeanTwist hp.pos t).le)
  calc
    _ ≤ ∑ S ∈ J.powerset,
        ‖LSeries (gsA9Low (primeBandCoefficient g (fun p ↦ p ∉ S.biUnion B)) y)
            ((sigmaLow : ℂ) + Complex.I * (t : ℂ)) *
          LSeries (gsA9High f y) (halaszPoint X t)‖ := hfirst
    _ ≤ ∑ S ∈ J.powerset, Real.exp (6 * gsA9WideSourceShiftConstant) *
        ‖LSeries (primeBandCoefficient g (fun p ↦ p ∉ S.biUnion B)) (halaszPoint X t)‖ :=
      Finset.sum_le_sum hmask
    _ = Real.exp (6 * gsA9WideSourceShiftConstant) *
        ∑ S ∈ J.powerset,
          ‖LSeries (primeBandCoefficient g (fun p ↦ p ∉ S.biUnion B)) (halaszPoint X t)‖ := by
      rw [Finset.mul_sum]
    _ ≤ Real.exp (6 * gsA9WideSourceShiftConstant) *
        Real.exp (Real.log (riemannZeta (taoExponent X : ℂ)).re +
          3 * primeQuadraticConstant + mrMaskProductSeries -
          Real.exp (-1) / 16 * pretentiousDistSq g (archimedeanTwist t) X) :=
      mul_le_mul_of_nonneg_left hsum (Real.exp_pos _).le
    _ ≤ _ := by
      unfold mrCofactorEulerBase
      rw [← Real.exp_add, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hh := mul_le_mul_of_nonneg_left hdist
        (show 0 ≤ Real.exp (-1) / 16 by positivity)
      dsimp only [g]
      linarith


theorem mrNorm_typicalCofactorLow_mul_high_le_inverseDistance
    (A : Finset ℕ) (hA : ∀ p ∈ A, p.Prime)
    (J : Finset ℕ) (B : ℕ → Finset ℕ) {X y : ℕ} (hX : 1 < X) (hy : 23 ≤ y)
    (hJ : ∀ j ∈ J, 1 ≤ j) (hB : ∀ j ∈ J, B j ⊆ primesUpTo X)
    (hdisj : Set.PairwiseDisjoint (↑J : Set ℕ) B)
    (hsmall : ∀ j ∈ J, ∀ p ∈ B j, Real.log (p : ℝ) ≤ Real.log (X : ℝ) / 16)
    (hmass : ∀ j ∈ J, 2 * Real.log (j : ℝ) ≤ ∑ p ∈ B j, 1 / (p : ℝ))
    (hAy : ∀ p ∈ A, p ≤ y) (hBy : ∀ j ∈ J, ∀ p ∈ B j, p ≤ y)
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (hfixed : primeBandCoefficient f (fun p ↦ 23 ≤ p) = f)
    {sigmaLow : ℝ} (hhalf : 1 / 2 ≤ sigmaLow)
    (hle : sigmaLow ≤ taoExponent X)
    (hsigma : 1 - 3 / Real.log (y : ℝ) ≤ sigmaLow)
    (hgap : taoExponent X - sigmaLow ≤ 3 / Real.log (y : ℝ))
    (t : ℝ) (hD : 0 < pretentiousDistSq f (archimedeanTwist t) X) :
    ‖LSeries (mrTypicalCofactorLowArithmetic A J B f y)
          ((sigmaLow : ℂ) + I * (t : ℂ)) *
        LSeries (gsA9High f y) (halaszPoint X t)‖ ≤
      mrCofactorEulerBase X *
        ((Real.exp (-1) / 16) * pretentiousDistSq f (archimedeanTwist t) X)⁻¹ := by
  let D := pretentiousDistSq f (archimedeanTwist t) X
  let c := Real.exp (-1) / 16
  let F : ℝ → ℂ := fun u ↦
    LSeries (gsA9Low (mrIndexedTypicalCoefficient J B (mrPrimeScaledCoefficient A f u)) y)
        ((sigmaLow : ℂ) + I * (t : ℂ)) * LSeries (gsA9High f y) (halaszPoint X t)
  let G : ℝ → ℝ := fun u ↦ mrCofactorEulerBase X * Real.exp (-c * u * D)
  have hsLow : 0 < ((sigmaLow : ℂ) + I * (t : ℂ)).re := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.I_im, Complex.ofReal_im, zero_mul, one_mul, sub_zero, add_zero]
    linarith
  rw [mrLSeries_typicalCofactorLow_eq_intervalIntegral A J B hbound y hsLow,
    ← intervalIntegral.integral_mul_const]
  have hmajor : ∀ u ∈ Icc (0 : ℝ) 1, ‖F u‖ ≤ G u := by
    intro u hu
    exact mrNorm_scaledTypicalLow_mul_high_le_scaleDistance A hA J B hX hy hJ hB hdisj
      hsmall hmass hAy hBy hmul hbound hfixed hhalf hle hsigma hgap hu.1 hu.2 t
  have hG : Continuous G := by dsimp only [G]; fun_prop
  have hnorm : ‖∫ u : ℝ in 0..1, F u‖ ≤ ∫ u : ℝ in 0..1, G u := by
    apply intervalIntegral.norm_integral_le_of_norm_le (by norm_num)
    · filter_upwards with u
      intro hu
      exact hmajor u ⟨hu.1.le, hu.2⟩
    · exact hG.intervalIntegrable _ _
  change ‖∫ u : ℝ in 0..1, F u‖ ≤ _
  calc
    _ ≤ ∫ u : ℝ in 0..1, G u := hnorm
    _ = mrCofactorEulerBase X * ∫ u : ℝ in 0..1, Real.exp (-c * u * D) := by
      dsimp only [G]
      rw [intervalIntegral.integral_const_mul]
    _ ≤ mrCofactorEulerBase X * (c * D)⁻¹ :=
      mul_le_mul_of_nonneg_left (mrIntegral_exp_scaledDistance_le_inv (by dsimp [c]; positivity) hD)
        (Real.exp_pos _).le

theorem mrNorm_sourceTypicalCofactorLow_mul_high_le_averageEnvelope
    (A : Finset ℕ) (hA : ∀ p ∈ A, p.Prime)
    (J : Finset ℕ) (B : ℕ → Finset ℕ) {N X y : ℕ}
    (hN : 0 < N) (hX : 1 < X) (hy : 23 ≤ y)
    (hJ : ∀ j ∈ J, 1 ≤ j) (hB : ∀ j ∈ J, B j ⊆ primesUpTo X)
    (hdisj : Set.PairwiseDisjoint (↑J : Set ℕ) B)
    (hsmall : ∀ j ∈ J, ∀ p ∈ B j, Real.log (p : ℝ) ≤ Real.log (X : ℝ) / 16)
    (hmass : ∀ j ∈ J, 2 * Real.log (j : ℝ) ≤ ∑ p ∈ B j, 1 / (p : ℝ))
    (hAy : ∀ p ∈ A, p ≤ y) (hBy : ∀ j ∈ J, ∀ p ∈ B j, p ≤ y)
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1) (hnonpret : MRArchimedeanNonpretentious f N X)
    {alpha beta t : ℝ} (hlogy : 6 ≤ Real.log (y : ℝ))
    (ha0 : 0 ≤ alpha) (ha : alpha ≤ (Real.log (y : ℝ))⁻¹)
    (hb0 : 0 ≤ beta) (hb : beta ≤ (Real.log (y : ℝ))⁻¹) (ht : |t| ≤ X) :
    ‖LSeries (mrTypicalCofactorLowArithmetic A J B (gsDeletePrimeBand f gsA9SmallPrime) y)
          (((taoExponent X - alpha - 2 * beta : ℝ) : ℂ) + I * (t : ℂ)) *
        LSeries (gsA9High f y) (halaszPoint X t)‖ ≤ mrCofactorAverageEnvelope N X := by
  let g := gsDeletePrimeBand f gsA9SmallPrime
  have hfixed : primeBandCoefficient g (fun p ↦ 23 ≤ p) = g := by
    dsimp only [g]
    rw [mrDeleteSmallPrimes_eq_largePrimeBand, mrPrimeBandCoefficient_idempotent]
  have hdist := archimedeanNonpretentious_half_deleteSmallPrimes hbound hnonpret t ht
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hD : 0 < pretentiousDistSq g (archimedeanTwist t) X :=
    (by linarith : (0 : ℝ) < (N : ℝ) / 2).trans_le hdist
  have hc := one_lt_taoExponent hX
  have hinv : (Real.log (y : ℝ))⁻¹ ≤ 1 / 6 := by
    simpa only [one_div] using inv_anti₀ (by norm_num : (0 : ℝ) < 6) hlogy
  have hpoint := mrNorm_typicalCofactorLow_mul_high_le_inverseDistance A hA J B hX hy hJ hB
    hdisj hsmall hmass hAy hBy
    (gsDeletePrimeBand_isMultiplicativeOnPositiveNat hmul gsA9SmallPrime)
    (fun n hn ↦ norm_gsDeletePrimeBand_le_one hbound gsA9SmallPrime hn) hfixed
    (sigmaLow := taoExponent X - alpha - 2 * beta)
    (by linarith) (by linarith)
    (by simp only [div_eq_mul_inv]; linarith)
    (by simp only [div_eq_mul_inv]; linarith) t hD
  rw [gsA9High_deleteSmallPrimes_eq f hy] at hpoint
  apply hpoint.trans
  unfold mrCofactorAverageEnvelope
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  exact inv_anti₀ (by positivity)
    (mul_le_mul_of_nonneg_left hdist (by positivity))

end

end Erdos67b
