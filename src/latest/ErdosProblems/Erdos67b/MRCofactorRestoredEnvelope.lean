import ErdosProblems.Erdos67b.MRTypicalSmallPrimeRestore
import ErdosProblems.Erdos67b.MRCofactorDistanceEnvelope

/-!
# The averaged cofactor envelope for the original coefficient

The fixed small-prime factor is restored in each scaled low series before
the denominator average. Its uniform bound is independent of the scale,
even when the denominator prime set contains small primes.
-/

open scoped BigOperators
open Complex Set MeasureTheory

namespace Erdos67b

open MRHalaszBands MRHalaszEuler EulerResidue BoundedGaps.Maynard

noncomputable section

theorem mrCofactorSmallPrimeConstant_nonneg : 0 ≤ gsA9SmallPrimeEulerBound := by
  have h := norm_gsA9SmallPrimeEulerProduct_le (f := fun _ : ℕ ↦ (0 : ℂ))
    (fun _ _ ↦ by simp) (sigma := (1 / 2 : ℝ)) (t := 0) le_rfl
  exact (norm_nonneg _).trans h

def mrCofactorRestoredEnvelope (N X : ℕ) : ℝ :=
  gsA9SmallPrimeEulerBound * mrCofactorAverageEnvelope N X

theorem mrCofactorRestoredEnvelope_nonneg (N X : ℕ) :
    0 ≤ mrCofactorRestoredEnvelope N X := by
  unfold mrCofactorRestoredEnvelope
  apply mul_nonneg mrCofactorSmallPrimeConstant_nonneg
  unfold mrCofactorAverageEnvelope mrCofactorEulerBase
  positivity

theorem mrNorm_restoredScaledTypicalLow_mul_high_le_scaleDistance
    (A : Finset ℕ) (hA : ∀ p ∈ A, p.Prime)
    (J : Finset ℕ) (B : ℕ → Finset ℕ) {X y : ℕ} (hX : 1 < X) (hy : 23 ≤ y)
    (hJ : ∀ j ∈ J, 1 ≤ j) (hB : ∀ j ∈ J, B j ⊆ primesUpTo X)
    (hdisj : Set.PairwiseDisjoint (↑J : Set ℕ) B)
    (hsmall : ∀ j ∈ J, ∀ p ∈ B j, Real.log (p : ℝ) ≤ Real.log (X : ℝ) / 16)
    (hmass : ∀ j ∈ J, 2 * Real.log (j : ℝ) ≤ ∑ p ∈ B j, 1 / (p : ℝ))
    (hAy : ∀ p ∈ A, p ≤ y) (hBy : ∀ j ∈ J, ∀ p ∈ B j, p ≤ y)
    (hlarge : ∀ j ∈ J, ∀ p ∈ B j, 23 ≤ p)
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {sigmaLow u : ℝ} (hhalf : 1 / 2 ≤ sigmaLow)
    (hle : sigmaLow ≤ taoExponent X)
    (hsigma : 1 - 3 / Real.log (y : ℝ) ≤ sigmaLow)
    (hgap : taoExponent X - sigmaLow ≤ 3 / Real.log (y : ℝ))
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (t : ℝ) :
    ‖LSeries (gsA9Low (mrIndexedTypicalCoefficient J B (mrPrimeScaledCoefficient A f u)) y)
          ((sigmaLow : ℂ) + I * (t : ℂ)) * LSeries (gsA9High f y) (halaszPoint X t)‖ ≤
      (gsA9SmallPrimeEulerBound * mrCofactorEulerBase X) *
        Real.exp (-(Real.exp (-1) / 16) * u *
          pretentiousDistSq (gsDeletePrimeBand f gsA9SmallPrime) (archimedeanTwist t) X) := by
  let g := gsDeletePrimeBand f gsA9SmallPrime
  have hfixed : primeBandCoefficient g (fun p ↦ 23 ≤ p) = g := by
    dsimp only [g]
    rw [mrDeleteSmallPrimes_eq_largePrimeBand, mrPrimeBandCoefficient_idempotent]
  have hpoint := mrNorm_scaledTypicalLow_mul_high_le_scaleDistance A hA J B hX hy hJ hB
    hdisj hsmall hmass hAy hBy
    (gsDeletePrimeBand_isMultiplicativeOnPositiveNat hmul gsA9SmallPrime)
    (fun n hn ↦ norm_gsDeletePrimeBand_le_one hbound gsA9SmallPrime hn)
    hfixed hhalf hle hsigma hgap hu0 hu1 t
  rw [gsA9High_deleteSmallPrimes_eq f hy] at hpoint
  have hsLow : 0 < ((sigmaLow : ℂ) + I * (t : ℂ)).re := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.I_im, Complex.ofReal_im, zero_mul, one_mul, sub_zero, add_zero]
    linarith
  have hrestore := mrLSeries_low_scaledTypical_eq_smallPrime_mul_delete A hA J B
    (fun j hj p hp ↦ (mem_primesUpTo.mp (hB j hj hp)).1) hlarge hmul hbound hy hu0 hu1 hsLow
  have hsmallEuler := norm_gsA9SmallPrimeEulerProduct_le
    (f := mrPrimeScaledCoefficient A f u)
    (fun n hn ↦ norm_mrPrimeScaledCoefficient_le_one hbound hu0 hu1 hn)
    (sigma := sigmaLow) (t := t) hhalf
  rw [hrestore, mul_assoc, norm_mul]
  calc
    _ ≤ gsA9SmallPrimeEulerBound *
        ‖LSeries (gsA9Low (mrIndexedTypicalCoefficient J B (mrPrimeScaledCoefficient A g u)) y)
            ((sigmaLow : ℂ) + I * (t : ℂ)) * LSeries (gsA9High f y) (halaszPoint X t)‖ :=
      mul_le_mul_of_nonneg_right hsmallEuler (norm_nonneg _)
    _ ≤ gsA9SmallPrimeEulerBound * (mrCofactorEulerBase X *
        Real.exp (-(Real.exp (-1) / 16) * u * pretentiousDistSq g (archimedeanTwist t) X)) :=
      mul_le_mul_of_nonneg_left hpoint mrCofactorSmallPrimeConstant_nonneg
    _ = _ := by ring

theorem mrNorm_restoredTypicalCofactorLow_mul_high_le_inverseDistance
    (A : Finset ℕ) (hA : ∀ p ∈ A, p.Prime)
    (J : Finset ℕ) (B : ℕ → Finset ℕ) {X y : ℕ} (hX : 1 < X) (hy : 23 ≤ y)
    (hJ : ∀ j ∈ J, 1 ≤ j) (hB : ∀ j ∈ J, B j ⊆ primesUpTo X)
    (hdisj : Set.PairwiseDisjoint (↑J : Set ℕ) B)
    (hsmall : ∀ j ∈ J, ∀ p ∈ B j, Real.log (p : ℝ) ≤ Real.log (X : ℝ) / 16)
    (hmass : ∀ j ∈ J, 2 * Real.log (j : ℝ) ≤ ∑ p ∈ B j, 1 / (p : ℝ))
    (hAy : ∀ p ∈ A, p ≤ y) (hBy : ∀ j ∈ J, ∀ p ∈ B j, p ≤ y)
    (hlarge : ∀ j ∈ J, ∀ p ∈ B j, 23 ≤ p)
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {sigmaLow : ℝ} (hhalf : 1 / 2 ≤ sigmaLow)
    (hle : sigmaLow ≤ taoExponent X)
    (hsigma : 1 - 3 / Real.log (y : ℝ) ≤ sigmaLow)
    (hgap : taoExponent X - sigmaLow ≤ 3 / Real.log (y : ℝ))
    (t : ℝ) (hD : 0 < pretentiousDistSq (gsDeletePrimeBand f gsA9SmallPrime) (archimedeanTwist t) X) :
    ‖LSeries (mrTypicalCofactorLowArithmetic A J B f y)
          ((sigmaLow : ℂ) + I * (t : ℂ)) * LSeries (gsA9High f y) (halaszPoint X t)‖ ≤
      (gsA9SmallPrimeEulerBound * mrCofactorEulerBase X) *
        ((Real.exp (-1) / 16) *
          pretentiousDistSq (gsDeletePrimeBand f gsA9SmallPrime) (archimedeanTwist t) X)⁻¹ := by
  let D := pretentiousDistSq (gsDeletePrimeBand f gsA9SmallPrime) (archimedeanTwist t) X
  let c := Real.exp (-1) / 16
  let E := gsA9SmallPrimeEulerBound * mrCofactorEulerBase X
  let F : ℝ → ℂ := fun u ↦
    LSeries (gsA9Low (mrIndexedTypicalCoefficient J B (mrPrimeScaledCoefficient A f u)) y)
      ((sigmaLow : ℂ) + I * (t : ℂ)) * LSeries (gsA9High f y) (halaszPoint X t)
  let G : ℝ → ℝ := fun u ↦ E * Real.exp (-c * u * D)
  have hE : 0 ≤ E := mul_nonneg mrCofactorSmallPrimeConstant_nonneg (Real.exp_pos _).le
  have hsLow : 0 < ((sigmaLow : ℂ) + I * (t : ℂ)).re := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.I_im, Complex.ofReal_im, zero_mul, one_mul, sub_zero, add_zero]
    linarith
  rw [mrLSeries_typicalCofactorLow_eq_intervalIntegral A J B hbound y hsLow,
    ← intervalIntegral.integral_mul_const]
  have hmajor : ∀ u ∈ Icc (0 : ℝ) 1, ‖F u‖ ≤ G u := by
    intro u hu
    exact mrNorm_restoredScaledTypicalLow_mul_high_le_scaleDistance A hA J B hX hy hJ hB
      hdisj hsmall hmass hAy hBy hlarge hmul hbound hhalf hle hsigma hgap hu.1 hu.2 t
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
    _ = E * ∫ u : ℝ in 0..1, Real.exp (-c * u * D) := by
      dsimp only [G]
      rw [intervalIntegral.integral_const_mul]
    _ ≤ E * (c * D)⁻¹ := mul_le_mul_of_nonneg_left
      (mrIntegral_exp_scaledDistance_le_inv (by dsimp only [c]; positivity) hD) hE

theorem mrNorm_sourceRestoredTypicalCofactorLow_mul_high_le_envelope_of_distance
    (A : Finset ℕ) (hA : ∀ p ∈ A, p.Prime)
    (J : Finset ℕ) (B : ℕ → Finset ℕ) {N X y : ℕ}
    (hN : 0 < N) (hX : 1 < X) (hy : 23 ≤ y)
    (hJ : ∀ j ∈ J, 1 ≤ j) (hB : ∀ j ∈ J, B j ⊆ primesUpTo X)
    (hdisj : Set.PairwiseDisjoint (↑J : Set ℕ) B)
    (hsmall : ∀ j ∈ J, ∀ p ∈ B j, Real.log (p : ℝ) ≤ Real.log (X : ℝ) / 16)
    (hmass : ∀ j ∈ J, 2 * Real.log (j : ℝ) ≤ ∑ p ∈ B j, 1 / (p : ℝ))
    (hAy : ∀ p ∈ A, p ≤ y) (hBy : ∀ j ∈ J, ∀ p ∈ B j, p ≤ y)
    (hlarge : ∀ j ∈ J, ∀ p ∈ B j, 23 ≤ p)
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {alpha beta t : ℝ} (hlogy : 6 ≤ Real.log (y : ℝ))
    (ha0 : 0 ≤ alpha) (ha : alpha ≤ (Real.log (y : ℝ))⁻¹)
    (hb0 : 0 ≤ beta) (hb : beta ≤ (Real.log (y : ℝ))⁻¹)
    (hdistance : (N : ℝ) ≤ pretentiousDistSq f (archimedeanTwist t) X) :
    ‖LSeries (mrTypicalCofactorLowArithmetic A J B f y)
          (((taoExponent X - alpha - 2 * beta : ℝ) : ℂ) + I * (t : ℂ)) *
        LSeries (gsA9High f y) (halaszPoint X t)‖ ≤ mrCofactorRestoredEnvelope N X := by
  have hdist : (N : ℝ) / 2 ≤
      pretentiousDistSq (gsDeletePrimeBand f gsA9SmallPrime) (archimedeanTwist t) X :=
    (div_le_div_of_nonneg_right hdistance (by norm_num)).trans
      (half_pretentiousDistSq_le_deletePrimeBand
        (fun p hp ↦ hbound p hp.pos)
        (fun p hp ↦ by rw [norm_archimedeanTwist hp.pos]) gsA9SmallPrime X)
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hD : 0 < pretentiousDistSq (gsDeletePrimeBand f gsA9SmallPrime) (archimedeanTwist t) X :=
    (by linarith : (0 : ℝ) < (N : ℝ) / 2).trans_le hdist
  have hc := one_lt_taoExponent hX
  have hinv : (Real.log (y : ℝ))⁻¹ ≤ 1 / 6 := by
    simpa only [one_div] using inv_anti₀ (by norm_num : (0 : ℝ) < 6) hlogy
  have hpoint := mrNorm_restoredTypicalCofactorLow_mul_high_le_inverseDistance
    A hA J B hX hy hJ hB hdisj hsmall hmass hAy hBy hlarge hmul hbound
    (sigmaLow := taoExponent X - alpha - 2 * beta)
    (by linarith) (by linarith)
    (by simp only [div_eq_mul_inv]; linarith)
    (by simp only [div_eq_mul_inv]; linarith) t hD
  apply hpoint.trans
  unfold mrCofactorRestoredEnvelope mrCofactorAverageEnvelope
  rw [← mul_assoc]
  apply mul_le_mul_of_nonneg_left _
    (mul_nonneg mrCofactorSmallPrimeConstant_nonneg (Real.exp_pos _).le)
  exact inv_anti₀ (by positivity) (mul_le_mul_of_nonneg_left hdist (by positivity))

theorem mrNorm_sourceRestoredTypicalCofactorLow_mul_high_le_envelope
    (A : Finset ℕ) (hA : ∀ p ∈ A, p.Prime)
    (J : Finset ℕ) (B : ℕ → Finset ℕ) {N X y : ℕ}
    (hN : 0 < N) (hX : 1 < X) (hy : 23 ≤ y)
    (hJ : ∀ j ∈ J, 1 ≤ j) (hB : ∀ j ∈ J, B j ⊆ primesUpTo X)
    (hdisj : Set.PairwiseDisjoint (↑J : Set ℕ) B)
    (hsmall : ∀ j ∈ J, ∀ p ∈ B j, Real.log (p : ℝ) ≤ Real.log (X : ℝ) / 16)
    (hmass : ∀ j ∈ J, 2 * Real.log (j : ℝ) ≤ ∑ p ∈ B j, 1 / (p : ℝ))
    (hAy : ∀ p ∈ A, p ≤ y) (hBy : ∀ j ∈ J, ∀ p ∈ B j, p ≤ y)
    (hlarge : ∀ j ∈ J, ∀ p ∈ B j, 23 ≤ p)
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1) (hnonpret : MRArchimedeanNonpretentious f N X)
    {alpha beta t : ℝ} (hlogy : 6 ≤ Real.log (y : ℝ))
    (ha0 : 0 ≤ alpha) (ha : alpha ≤ (Real.log (y : ℝ))⁻¹)
    (hb0 : 0 ≤ beta) (hb : beta ≤ (Real.log (y : ℝ))⁻¹) (ht : |t| ≤ X) :
    ‖LSeries (mrTypicalCofactorLowArithmetic A J B f y)
          (((taoExponent X - alpha - 2 * beta : ℝ) : ℂ) + I * (t : ℂ)) *
        LSeries (gsA9High f y) (halaszPoint X t)‖ ≤ mrCofactorRestoredEnvelope N X :=
  mrNorm_sourceRestoredTypicalCofactorLow_mul_high_le_envelope_of_distance
    A hA J B hN hX hy hJ hB hdisj hsmall hmass hAy hBy hlarge hmul hbound
    hlogy ha0 ha hb0 hb (hnonpret t ht)

end

end Erdos67b
