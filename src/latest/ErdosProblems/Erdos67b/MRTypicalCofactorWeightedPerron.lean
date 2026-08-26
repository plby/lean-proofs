import ErdosProblems.Erdos67b.MRCofactorWeightedLambda
import ErdosProblems.Erdos67b.MRTypicalCofactorSecondaries

/-!
# Weighted Perron estimate for the actual typical cofactor

The variable power is part of the bounded numerator. The Perron denominator
remains in the prime energies, so no factor proportional to the vertical
height is charged to the prime main term.
-/

open scoped BigOperators Classical LSeries.notation
open Complex

namespace Erdos67b

open MRHalaszBands MRHalaszEuler EulerResidue EulerQuantitative BoundedGaps.Maynard

noncomputable section

theorem mrExists_norm_typicalCofactorMovingPerronIntegral_weighted_le :
    ∃ C : ℝ, ∃ Y : ℕ, 1 ≤ C ∧
      ∀ (A : Finset ℕ) (_hA : ∀ p ∈ A, p.Prime)
        (J : Finset ℕ) (B : ℕ → Finset ℕ) {N X y : ℕ}
        (_hY : Y ≤ y) (_hX : 2 ≤ X) (_hy : 23 ≤ y)
        (_hJ : ∀ j ∈ J, 1 ≤ j) (_hB : ∀ j ∈ J, B j ⊆ primesUpTo X)
        (_hdisj : Set.PairwiseDisjoint (↑J : Set ℕ) B)
        (_hsmall : ∀ j ∈ J, ∀ p ∈ B j, Real.log (p : ℝ) ≤ Real.log (X : ℝ) / 16)
        (_hmass : ∀ j ∈ J, 2 * Real.log (j : ℝ) ≤ ∑ p ∈ B j, 1 / (p : ℝ))
        (_hAy : ∀ p ∈ A, p ≤ y) (_hBy : ∀ j ∈ J, ∀ p ∈ B j, p ≤ y)
        {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
        (_hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1) (_hnonpret : MRArchimedeanNonpretentious f N X)
        {alpha beta T : ℝ} (K : ℕ) (_hlogy : 6 ≤ Real.log (y : ℝ))
        (_ha0 : 0 ≤ alpha) (_ha : alpha ≤ (Real.log (y : ℝ))⁻¹)
        (_hb0 : 0 ≤ beta) (_hb : beta ≤ (Real.log (y : ℝ))⁻¹)
        (_hT : 0 ≤ T) (_hTX : T ≤ X) (_hTK : T ≤ (((2 : ℕ) ^ K : ℕ) : ℝ)),
        ‖mrTypicalCofactorMovingPerronIntegral A J B (gsDeletePrimeBand f gsA9SmallPrime)
          (gsDeletePrimeBand_isMultiplicativeOnPositiveNat hmul gsA9SmallPrime)
          y X alpha beta T‖ ≤
          (2 * Real.pi)⁻¹ *
            (mrTypicalCofactorFixedHighEnvelope A N X *
              (X : ℝ) ^ (taoExponent X - alpha - 2 * beta)) *
            (gsA10PrimeSourceWeightedRowFactor C y X K *
                (((X / y : ℕ) : ℝ) ^ (2 * beta) * gsA10PrimeLambdaHarmonicBudget X) +
              4 * T * gsA10LambdaVerticalSplitError y X
                (taoExponent X - 2 * beta) (taoExponent X)) := by
  obtain ⟨C, Y, hC, hvertical⟩ := mrExists_weightedLambda_fixedHigh_pair_le
  refine ⟨C, Y, hC, ?_⟩
  intro A hA J B N X y hY hX hy hJ hB hdisj hsmall hmass hAy hBy f hmul hbound hnonpret
    alpha beta T K hlogy ha0 ha hb0 hb hT hTX hTK
  let g := gsDeletePrimeBand f gsA9SmallPrime
  let hgmul := gsDeletePrimeBand_isMultiplicativeOnPositiveNat hmul gsA9SmallPrime
  have hgbound : ∀ n, 0 < n → ‖g n‖ ≤ 1 :=
    fun n hn ↦ norm_gsDeletePrimeBand_le_one hbound gsA9SmallPrime hn
  let sigma := taoExponent X - alpha - 2 * beta
  let M := mrTypicalCofactorFixedHighEnvelope A N X
  let s : ℝ → ℂ := fun t ↦ (sigma : ℂ) + I * (t : ℂ)
  let lowHigh : ℝ → ℂ := fun t ↦
    LSeries (mrTypicalCofactorLowArithmetic A J B g y) (s t) *
      LSeries (gsA9HighArithmetic g y) (halaszPoint X t)
  let F : ℝ → ℂ := fun t ↦ lowHigh t * (X : ℂ) ^ s t
  have hc := one_lt_taoExponent (show 1 < X by omega)
  have hinv : (Real.log (y : ℝ))⁻¹ ≤ 1 / 6 := by
    simpa only [one_div] using inv_anti₀ (by norm_num : (0 : ℝ) < 6) hlogy
  have hhalf : 1 / 2 ≤ sigma := by dsimp only [sigma]; linarith
  have hsigma : 0 < sigma := by linarith
  have hM : 0 ≤ M := (Real.exp_pos _).le
  have hXR : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hs : Continuous s := by dsimp only [s]; fun_prop
  have hcont : Continuous F :=
    ((mrContinuous_LSeries_typicalCofactorLow_vertical A J B hgbound y hsigma).mul
      (continuous_LSeries_gsA9HighArithmetic_vertical hgbound y hc)).mul
        (continuous_const.cpow hs (fun _ ↦ Or.inl (by exact_mod_cast (show 0 < X by omega))))
  have hlowBound : ∀ t, |t| ≤ T → ‖lowHigh t‖ ≤ M := by
    intro t ht
    dsimp only [lowHigh]
    rw [LSeries_gsA9HighArithmetic, gsA9High_deleteSmallPrimes_eq f hy]
    exact mrNorm_sourceTypicalCofactorLow_mul_high_fixedHalasz_le A hA J B (by omega) hy hJ hB
      hdisj hsmall hmass hAy hBy hmul hbound hnonpret hlogy ha0 ha hb0 hb (ht.trans hTX)
  have hFbound : ∀ t, |t| ≤ T → ‖F t‖ ≤ M * (X : ℝ) ^ sigma := by
    intro t ht
    have hpow : ‖(X : ℂ) ^ s t‖ = (X : ℝ) ^ sigma := by
      simpa [s] using Complex.norm_cpow_eq_rpow_re_of_pos hXR (s t)
    dsimp only [F]
    rw [norm_mul, hpow]
    exact mul_le_mul_of_nonneg_right (hlowBound t ht) (Real.rpow_nonneg hXR.le _)
  have hraw := hvertical hgmul hgbound y X beta sigma T (M * (X : ℝ) ^ sigma) K F
    hY hX hb0 hhalf hT hTK (mul_nonneg hM (Real.rpow_nonneg hXR.le _)) hcont hFbound
  have hcontour : mrTypicalCofactorMovingPerronIntegral A J B g hgmul y X alpha beta T =
      (((2 * Real.pi : ℝ) : ℂ)⁻¹) * ∫ t in -T..T,
        F t * LSeries (gsA10LambdaWindow (gsA9HighGeneralizedMangoldt hgmul y) y X)
            (((taoExponent X - 2 * beta : ℝ) : ℂ) + I * (t : ℂ)) *
          LSeries (gsA10LambdaWindow (gsA9HighGeneralizedMangoldt hgmul y) y X)
            ((taoExponent X : ℂ) + I * (t : ℂ)) / s t := by
    rw [mrTypicalCofactorMovingPerronIntegral_eq_fourFactors A J B hgmul hgbound
      (by omega) hlogy ha hb]
    congr 1
    apply intervalIntegral.integral_congr
    intro t _
    dsimp only [F, lowHigh, s, sigma, halaszPoint]
    ring
  rw [hcontour, norm_mul]
  have hscalar : ‖(((2 * Real.pi : ℝ) : ℂ)⁻¹)‖ = (2 * Real.pi)⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  rw [hscalar]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hraw (inv_nonneg.mpr (by positivity))

end

end Erdos67b
