import ErdosProblems.Erdos67b.MRLowMaskInclusion
import ErdosProblems.Erdos67b.MRLowCofactorIntegral

/-!
# Summed masked low factors on the fixed-high contour

The low shift is bounded before any square root.  Inclusion-exclusion and
the denominator average therefore retain the summable deleted-prime cost.
The theorem is about the actual low/high factor in the Perron integrand,
not a finite-polynomial endpoint.
-/

open scoped BigOperators Classical Interval LSeries.notation
open Finset

namespace Erdos67b

open MRHalaszBands MRHalaszEuler EulerResidue EulerQuantitative

noncomputable section

theorem mrPrimeBandCoefficient_idempotent (f : ℕ → ℂ)
    (P : ℕ → Prop) [DecidablePred P] :
    primeBandCoefficient (primeBandCoefficient f P) P = primeBandCoefficient f P := by
  rw [primeBandCoefficient_nested]
  exact primeBandCoefficient_congr_pred f _ _ (fun _ ↦ by tauto)

theorem mrPrimeScaled_largePrimeSupported
    (A : Finset ℕ) {f : ℕ → ℂ}
    (hfixed : primeBandCoefficient f (fun p ↦ 23 ≤ p) = f) (u : ℝ) :
    primeBandCoefficient (mrPrimeScaledCoefficient A f u) (fun p ↦ 23 ≤ p) =
      mrPrimeScaledCoefficient A f u := by
  rw [← mrPrimeScaled_primeBandCoefficient, hfixed]

theorem mrNorm_maskedLow_mul_high_shift_le_of_largePrimeSupport
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (hfixed : primeBandCoefficient f (fun p ↦ 23 ≤ p) = f)
    (P : ℕ → Prop) [DecidablePred P] {y : ℕ} (hy : 23 ≤ y)
    (hsmall : ∀ p, ¬ P p → p ≤ y)
    {sigmaLow sigmaHigh t : ℝ} (hhalf : 1 / 2 ≤ sigmaLow)
    (hle : sigmaLow ≤ sigmaHigh)
    (hsigma : 1 - 3 / Real.log (y : ℝ) ≤ sigmaLow)
    (hgap : sigmaHigh - sigmaLow ≤ 3 / Real.log (y : ℝ))
    (hhigh : 1 < sigmaHigh) :
    ‖LSeries (gsA9Low (primeBandCoefficient f P) y)
          ((sigmaLow : ℂ) + Complex.I * (t : ℂ)) *
        LSeries (gsA9High f y) ((sigmaHigh : ℂ) + Complex.I * (t : ℂ))‖ ≤
      Real.exp (6 * gsA9WideSourceShiftConstant) *
        ‖LSeries (primeBandCoefficient f P)
          ((sigmaHigh : ℂ) + Complex.I * (t : ℂ))‖ := by
  have hmask : primeBandCoefficient f (fun p ↦ 23 ≤ p ∧ P p) =
      primeBandCoefficient f P := by
    rw [← primeBandCoefficient_nested, hfixed]
  have hsmall' : ∀ p, ¬ (23 ≤ p ∧ P p) → p ≤ y := by
    intro p hp
    by_cases hp23 : 23 ≤ p
    · exact hsmall p (fun hpP ↦ hp ⟨hp23, hpP⟩)
    · omega
  have hbase := mrNorm_maskedLow_mul_high_shift_le hmul hbound
    (fun p ↦ 23 ≤ p ∧ P p) (by omega : 2 ≤ y) hsmall'
    (fun _ _ hp ↦ hp.1) hhalf hle hsigma hgap hhigh (t := t)
  rwa [hmask] at hbase

/-- The whole low/high factor for a scaled typical coefficient, uniformly
over the denominator parameter. -/
theorem mrNorm_scaledTypicalLow_mul_high_le
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
      Real.exp (6 * gsA9WideSourceShiftConstant +
        Real.log (riemannZeta (taoExponent X : ℂ)).re +
        3 * primeQuadraticConstant + mrMaskProductSeries -
        Real.exp (-1) / 16 * pretentiousDistSq f (archimedeanTwist t) X +
        Real.exp (-1) / 16 * mrSelectedPrimeReciprocalMass A X) := by
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
  have hdist := pretentiousDistSq_le_scaled_add_mass (X := X) hA hu0 hu1
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
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hh := mul_le_mul_of_nonneg_left hdist
        (show 0 ≤ Real.exp (-1) / 16 by positivity)
      dsimp only [g]
      linarith

/-- The bound for the actual denominator-weighted typical low factor.
No absolute-convergence assumption is left at the left contour line. -/
theorem mrNorm_typicalCofactorLow_mul_high_le
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
    (hgap : taoExponent X - sigmaLow ≤ 3 / Real.log (y : ℝ)) (t : ℝ) :
    ‖LSeries (mrTypicalCofactorLowArithmetic A J B f y)
          ((sigmaLow : ℂ) + Complex.I * (t : ℂ)) *
        LSeries (gsA9High f y) (halaszPoint X t)‖ ≤
      Real.exp (6 * gsA9WideSourceShiftConstant +
        Real.log (riemannZeta (taoExponent X : ℂ)).re +
        3 * primeQuadraticConstant + mrMaskProductSeries -
        Real.exp (-1) / 16 * pretentiousDistSq f (archimedeanTwist t) X +
        Real.exp (-1) / 16 * mrSelectedPrimeReciprocalMass A X) := by
  have hsLow : 0 < ((sigmaLow : ℂ) + Complex.I * (t : ℂ)).re := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.I_im, Complex.ofReal_im, zero_mul, one_mul, sub_zero, add_zero]
    linarith
  rw [mrLSeries_typicalCofactorLow_eq_intervalIntegral A J B hbound y hsLow,
    ← intervalIntegral.integral_mul_const]
  have hpoint : ∀ u ∈ Ι (0 : ℝ) 1,
      ‖LSeries (gsA9Low (mrIndexedTypicalCoefficient J B (mrPrimeScaledCoefficient A f u)) y)
          ((sigmaLow : ℂ) + Complex.I * (t : ℂ)) *
        LSeries (gsA9High f y) (halaszPoint X t)‖ ≤
      Real.exp (6 * gsA9WideSourceShiftConstant +
        Real.log (riemannZeta (taoExponent X : ℂ)).re +
        3 * primeQuadraticConstant + mrMaskProductSeries -
        Real.exp (-1) / 16 * pretentiousDistSq f (archimedeanTwist t) X +
        Real.exp (-1) / 16 * mrSelectedPrimeReciprocalMass A X) := by
    intro u hu
    rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hu
    exact mrNorm_scaledTypicalLow_mul_high_le A hA J B hX hy hJ hB hdisj hsmall hmass
      hAy hBy hmul hbound hfixed hhalf hle hsigma hgap hu.1.le hu.2 t
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const hpoint
  simpa only [sub_zero, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1), mul_one] using hnorm

/-- Source-window specialization with all real-line location and gap
conditions discharged. -/
theorem mrNorm_typicalCofactorLow_mul_high_fixedHalasz_le
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
    {alpha beta : ℝ} (hlogy : 6 ≤ Real.log (y : ℝ))
    (ha0 : 0 ≤ alpha) (ha : alpha ≤ (Real.log (y : ℝ))⁻¹)
    (hb0 : 0 ≤ beta) (hb : beta ≤ (Real.log (y : ℝ))⁻¹) (t : ℝ) :
    ‖LSeries (mrTypicalCofactorLowArithmetic A J B f y)
          (((taoExponent X - alpha - 2 * beta : ℝ) : ℂ) + Complex.I * (t : ℂ)) *
        LSeries (gsA9High f y) (halaszPoint X t)‖ ≤
      Real.exp (6 * gsA9WideSourceShiftConstant +
        Real.log (riemannZeta (taoExponent X : ℂ)).re +
        3 * primeQuadraticConstant + mrMaskProductSeries -
        Real.exp (-1) / 16 * pretentiousDistSq f (archimedeanTwist t) X +
        Real.exp (-1) / 16 * mrSelectedPrimeReciprocalMass A X) := by
  have hc := one_lt_taoExponent hX
  have hinv : (Real.log (y : ℝ))⁻¹ ≤ 1 / 6 := by
    simpa only [one_div] using inv_anti₀ (by norm_num : (0 : ℝ) < 6) hlogy
  apply mrNorm_typicalCofactorLow_mul_high_le A hA J B hX hy hJ hB hdisj hsmall hmass
    hAy hBy hmul hbound hfixed
  · linarith
  · linarith
  · simp only [div_eq_mul_inv]
    linarith
  · simp only [div_eq_mul_inv]
    linarith

theorem mrDeleteSmallPrimes_eq_largePrimeBand (f : ℕ → ℂ) :
    gsDeletePrimeBand f gsA9SmallPrime = primeBandCoefficient f (fun p ↦ 23 ≤ p) := by
  funext n
  have hs : PrimeSupported (fun p ↦ ¬ gsA9SmallPrime p) n ↔
      PrimeSupported (fun p ↦ 23 ≤ p) n := by
    constructor
    · rintro ⟨hn, hprime⟩
      refine ⟨hn, fun p hp ↦ ?_⟩
      exact le_of_not_gt (fun hlt ↦ hprime p hp ⟨Nat.prime_of_mem_primeFactors hp, hlt⟩)
    · rintro ⟨hn, hprime⟩
      refine ⟨hn, fun p hp hsmall ↦ ?_⟩
      exact not_lt_of_ge (hprime p hp) hsmall.2
  unfold gsDeletePrimeBand primeBandCoefficient
  by_cases hn : PrimeSupported (fun p ↦ 23 ≤ p) n
  · rw [if_pos hn, if_pos (hs.mpr hn)]
  · rw [if_neg hn, if_neg (fun h ↦ hn (hs.mp h))]

/-- The concrete fixed small-prime deletion meets the support condition,
and nonpretentiousness of the original coefficient makes the bound uniform
in the vertical frequency. -/
theorem mrNorm_sourceTypicalCofactorLow_mul_high_fixedHalasz_le
    (A : Finset ℕ) (hA : ∀ p ∈ A, p.Prime)
    (J : Finset ℕ) (B : ℕ → Finset ℕ) {N X y : ℕ} (hX : 1 < X) (hy : 23 ≤ y)
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
          (((taoExponent X - alpha - 2 * beta : ℝ) : ℂ) + Complex.I * (t : ℂ)) *
        LSeries (gsA9High f y) (halaszPoint X t)‖ ≤
      Real.exp (6 * gsA9WideSourceShiftConstant +
        Real.log (riemannZeta (taoExponent X : ℂ)).re +
        3 * primeQuadraticConstant + mrMaskProductSeries -
        Real.exp (-1) / 16 * ((N : ℝ) / 2) +
        Real.exp (-1) / 16 * mrSelectedPrimeReciprocalMass A X) := by
  have hfixed : primeBandCoefficient (gsDeletePrimeBand f gsA9SmallPrime)
      (fun p ↦ 23 ≤ p) = gsDeletePrimeBand f gsA9SmallPrime := by
    rw [mrDeleteSmallPrimes_eq_largePrimeBand, mrPrimeBandCoefficient_idempotent]
  have hpoint := mrNorm_typicalCofactorLow_mul_high_fixedHalasz_le A hA J B hX hy hJ hB
    hdisj hsmall hmass hAy hBy
    (gsDeletePrimeBand_isMultiplicativeOnPositiveNat hmul gsA9SmallPrime)
    (fun n hn ↦ norm_gsDeletePrimeBand_le_one hbound gsA9SmallPrime hn)
    hfixed hlogy ha0 ha hb0 hb t
  rw [gsA9High_deleteSmallPrimes_eq f hy] at hpoint
  apply hpoint.trans
  apply Real.exp_le_exp.mpr
  have hdist := archimedeanNonpretentious_half_deleteSmallPrimes hbound hnonpret t ht
  have hh := mul_le_mul_of_nonneg_left hdist
    (show 0 ≤ Real.exp (-1) / 16 by positivity)
  linarith

end

end Erdos67b
