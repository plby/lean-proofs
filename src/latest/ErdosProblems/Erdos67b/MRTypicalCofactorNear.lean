import ErdosProblems.Erdos67b.MRTypicalCofactorProjection
import ErdosProblems.Erdos67b.MRGSA10TailoredNearMassOrdinary

/-!
# Coefficient and near-mass bounds for the actual typical cofactor

Complementary prime support extracts the unique shifted high factor from
the whole low coefficient. The two remaining generalized-Mangoldt windows
retain the exact ordinary prime and higher-prime-power majorants.
-/

open scoped BigOperators Classical
open Finset

namespace Erdos67b

open MRHalaszBands BoundedGaps.Maynard MRPerronNearTripleConvolution

noncomputable section

theorem mrTypicalCofactorLow_eq_zero_of_not_supported {ι : Type*}
    (A : Finset ℕ) (J : Finset ι) (B : ι → Finset ℕ) (f : ℕ → ℂ) (y : ℕ)
    {n : ℕ} (hn : n ≠ 0) (hnot : ¬ PrimeSupported (fun p ↦ p ≤ y) n) :
    mrTypicalCofactorLowArithmetic A J B f y n = 0 := by
  simp [mrTypicalCofactorLowArithmetic, toArithmeticFunction, gsA9Low,
    primeBandCoefficient, hn, hnot]

theorem mrTypicalCofactorSecondary_apply {ι : Type*}
    (A : Finset ℕ) (hA : ∀ p ∈ A, p.Prime) (J : Finset ι) (B : ι → Finset ℕ)
    (hB : ∀ j ∈ J, ∀ p ∈ B j, p.Prime)
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f) (y : ℕ)
    (hAy : ∀ p ∈ A, p ≤ y) (hBy : ∀ j ∈ J, ∀ p ∈ B j, p ≤ y)
    (rho : ℝ) {n : ℕ} (hn : 0 < n) :
    (mrTypicalCofactorLowArithmetic A J B f y * gsRealShift rho (gsA9HighArithmetic f y)) n =
      (((primeBandPart (fun p ↦ ¬ p ≤ y) n : ℝ) ^ (-rho) : ℝ) : ℂ) *
        mrIndexedTypicalCofactorCoefficient A J B f n := by
  have hhigh : ∀ e, e ≠ 0 → ¬ PrimeSupported (fun p ↦ ¬ p ≤ y) e →
      gsA9HighArithmetic f y e = 0 := by
    intro e he hnot
    rw [gsA9HighArithmetic_apply_of_ne_zero f y he]
    unfold gsA9High primeBandCoefficient
    rw [if_neg hnot]
  rw [low_mul_shift_high_apply _ _ y rho hn
    (fun d hd hnot ↦ mrTypicalCofactorLow_eq_zero_of_not_supported A J B f y hd hnot) hhigh,
    mrTypicalCofactorLowArithmetic_mul_high A hA J B hB hmul y hAy hBy]
  simp [toArithmeticFunction, hn.ne']

theorem mrNorm_typicalCofactorSecondary_le_one {ι : Type*}
    (A : Finset ℕ) (hA : ∀ p ∈ A, p.Prime) (J : Finset ι) (B : ι → Finset ℕ)
    (hB : ∀ j ∈ J, ∀ p ∈ B j, p.Prime)
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1) (y : ℕ)
    (hAy : ∀ p ∈ A, p ≤ y) (hBy : ∀ j ∈ J, ∀ p ∈ B j, p ≤ y)
    {rho : ℝ} (hrho : 0 ≤ rho) (n : ℕ) :
    ‖(mrTypicalCofactorLowArithmetic A J B f y * gsRealShift rho (gsA9HighArithmetic f y)) n‖ ≤ 1 := by
  by_cases hn : n = 0
  · subst n
    simp
  rw [mrTypicalCofactorSecondary_apply A hA J B hB hmul y hAy hBy rho (Nat.pos_of_ne_zero hn),
    norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
  have hweight : (primeBandPart (fun p ↦ ¬ p ≤ y) n : ℝ) ^ (-rho) ≤ 1 := by
    apply Real.rpow_le_one_of_one_le_of_nonpos
    · exact_mod_cast Nat.one_le_iff_ne_zero.mpr (primeBandPart_ne_zero (fun p ↦ ¬ p ≤ y) n)
    · linarith
  have hcoef := mrIndexedTypicalCofactorCoefficient_norm_le_one A J B hbound (Nat.pos_of_ne_zero hn)
  simpa only [one_mul] using mul_le_mul hweight hcoef (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)

theorem mrNorm_typicalCofactorTailored_apply_le_nested {ι : Type*}
    (A : Finset ℕ) (hA : ∀ p ∈ A, p.Prime) (J : Finset ι) (B : ι → Finset ℕ)
    (hB : ∀ j ∈ J, ∀ p ∈ B j, p.Prime)
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1) (y X : ℕ)
    (hAy : ∀ p ∈ A, p ≤ y) (hBy : ∀ j ∈ J, ∀ p ∈ B j, p ≤ y)
    {alpha beta : ℝ} (ha : 0 ≤ alpha) (hb : 0 ≤ beta) (n : ℕ) :
    ‖mrTypicalCofactorTailoredCoefficient A J B f hmul y X alpha beta n‖ ≤
      ∑ uv ∈ n.divisorsAntidiagonal, ∑ ab ∈ uv.1.divisorsAntidiagonal,
        gsA10OrdinaryLambdaNearWeight hmul y X alpha ab.1 *
          gsA10OrdinaryLambdaNearWeight hmul y X (alpha + 2 * beta) ab.2 := by
  let base := mrTypicalCofactorLowArithmetic A J B f y *
    gsRealShift (alpha + 2 * beta) (gsA9HighArithmetic f y)
  let W := gsA10LambdaWindow (gsA9HighGeneralizedMangoldt hmul y) y X
  have hraw := norm_mul_mul_apply_le_nested base (gsRealShift alpha W)
    (gsRealShift (alpha + 2 * beta) W) (fun _ ↦ (1 : ℝ))
    (gsA10OrdinaryLambdaNearWeight hmul y X alpha)
    (gsA10OrdinaryLambdaNearWeight hmul y X (alpha + 2 * beta))
    (mrNorm_typicalCofactorSecondary_le_one A hA J B hB hmul hbound y hAy hBy (by linarith))
    (norm_gsRealShift_gsA10LambdaWindow_le_ordinaryNearWeight hmul hbound y X ha)
    (norm_gsRealShift_gsA10LambdaWindow_le_ordinaryNearWeight hmul hbound y X (by linarith))
    (fun _ ↦ by norm_num)
    (gsA10OrdinaryLambdaNearWeight_nonneg hmul y X alpha)
    (gsA10OrdinaryLambdaNearWeight_nonneg hmul y X (alpha + 2 * beta)) n
  have hcoeff : mrTypicalCofactorTailoredCoefficient A J B f hmul y X alpha beta =
      (gsRealShift alpha W * gsRealShift (alpha + 2 * beta) W) * base := by
    unfold mrTypicalCofactorTailoredCoefficient gsA10TailoredCoefficient
    exact mul_comm _ _
  rw [hcoeff]
  simpa only [one_mul] using hraw

theorem mrDirichletPerronNearMass_typicalCofactorTailored_le {ι : Type*}
    (A : Finset ℕ) (hA : ∀ p ∈ A, p.Prime) (J : Finset ι) (B : ι → Finset ℕ)
    (hB : ∀ j ∈ J, ∀ p ∈ B j, p.Prime)
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1) {y X : ℕ}
    (hAy : ∀ p ∈ A, p ≤ y) (hBy : ∀ j ∈ J, ∀ p ∈ B j, p ≤ y)
    (hX : 0 < X) {T : ℝ} (hT : 0 < T)
    {alpha beta : ℝ} (ha : 0 ≤ alpha) (hb : 0 ≤ beta) :
    dirichletPerronNearMass (mrTypicalCofactorTailoredCoefficient A J B f hmul y X alpha beta) X T ≤
      ∑ a ∈ gsPositiveBelow (2 * X + 1),
        ∑ b ∈ (gsPositiveBelow (2 * X + 1)).filter (fun b ↦ a * b < 2 * X + 1),
          gsA10OrdinaryLambdaNearWeight hmul y X alpha a *
            gsA10OrdinaryLambdaNearWeight hmul y X (alpha + 2 * beta) b *
              (2 + (4 * (X : ℝ) / T) * ((a * b : ℕ) : ℝ)⁻¹ * (harmonic (2 * X) : ℝ)) := by
  let base := mrTypicalCofactorLowArithmetic A J B f y *
    gsRealShift (alpha + 2 * beta) (gsA9HighArithmetic f y)
  let W := gsA10LambdaWindow (gsA9HighGeneralizedMangoldt hmul y) y X
  have hraw := dirichletPerronNearMass_mul_mul_le hX hT base (gsRealShift alpha W)
    (gsRealShift (alpha + 2 * beta) W) (fun _ ↦ (1 : ℝ))
    (gsA10OrdinaryLambdaNearWeight hmul y X alpha)
    (gsA10OrdinaryLambdaNearWeight hmul y X (alpha + 2 * beta))
    (mrNorm_typicalCofactorSecondary_le_one A hA J B hB hmul hbound y hAy hBy (by linarith))
    (norm_gsRealShift_gsA10LambdaWindow_le_ordinaryNearWeight hmul hbound y X ha)
    (norm_gsRealShift_gsA10LambdaWindow_le_ordinaryNearWeight hmul hbound y X (by linarith))
    (fun _ ↦ by norm_num) (fun _ ↦ le_rfl)
    (gsA10OrdinaryLambdaNearWeight_nonneg hmul y X alpha)
    (gsA10OrdinaryLambdaNearWeight_nonneg hmul y X (alpha + 2 * beta))
  have hcoeff : mrTypicalCofactorTailoredCoefficient A J B f hmul y X alpha beta =
      (gsRealShift alpha W * gsRealShift (alpha + 2 * beta) W) * base := by
    unfold mrTypicalCofactorTailoredCoefficient gsA10TailoredCoefficient
    exact mul_comm _ _
  rw [hcoeff]
  exact hraw

end

end Erdos67b
