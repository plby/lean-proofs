import ErdosProblems.Erdos67b.MRPerronNearTripleConvolution
import ErdosProblems.Erdos67b.MRGSA10SpecializedPerron
import ErdosProblems.Erdos67b.MRGSA10SecondaryCoefficientMajorant
import ErdosProblems.Erdos67b.MRGSA10LambdaWindowMassOrdinary

/-!
# Ordinary-multiplicative near mass for the A.10 tailored coefficient

For an ordinary multiplicative coefficient, the generalized Mangoldt
coefficient agrees with the classical prime contribution only at primes.
This module retains the exact higher-prime-power part in two explicit,
nonnegative hyperbola weights.  Its reciprocal mass is controlled by the
already formalized geometric higher-prime-power estimate.
-/

open scoped BigOperators
open Finset

namespace Erdos67b.MRHalaszBands

noncomputable section

open BoundedGaps.Maynard
open MRPerronNearTripleConvolution

private theorem gsA10ShiuWeight_le_one_of_nonneg_ordinaryNear
    (y : ℕ) {rho : ℝ} (hrho : 0 ≤ rho) (n : ℕ) :
    gsA10ShiuWeight y rho n ≤ 1 := by
  unfold gsA10ShiuWeight
  split
  · exact zero_le_one
  · apply Real.rpow_le_one_of_one_le_of_nonpos
    · exact_mod_cast Nat.one_le_iff_ne_zero.mpr
        (primeBandPart_ne_zero (fun p ↦ ¬ p ≤ y) n)
    · exact neg_nonpos.mpr hrho

private theorem norm_gsA10TwoBlockLowHighShift_le_one_ordinaryNear
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂]
    (y : ℕ)
    (hQ₂ : ∀ p, (¬ P₁ p ∧ P₂ p) → p ≤ y)
    (hQ₃ : ∀ p, (¬ P₁ p ∧ ¬ P₂ p) → p ≤ y)
    {rho : ℝ} (hrho : 0 ≤ rho) (n : ℕ) :
    ‖(gsA10TwoBlockAlternatingLow f P₁ P₂ y *
        gsRealShift rho (gsA9HighArithmetic f y)) n‖ ≤ 1 := by
  by_cases hn : n = 0
  · subst n
    simp
  exact (norm_gsA10FirstSecondaryCoefficient_le_shiuWeight
    hmul hbound P₁ P₂ y hQ₂ hQ₃ rho (Nat.pos_of_ne_zero hn)).trans
      (gsA10ShiuWeight_le_one_of_nonneg_ordinaryNear y hrho n)

/-- Exact shifted prime majorant, including the strict finite Lambda-window
support.  It vanishes on composite prime powers and on primes outside the
source window. -/
def gsA10ShiftedPrimeLambdaWindowWeight
    (y X : ℕ) (rho : ℝ) (n : ℕ) : ℝ :=
  if y < n ∧ n < X / y then
    Real.exp (-rho * Real.log (n : ℝ)) *
      (if n.Prime then ArithmeticFunction.vonMangoldt n else 0)
  else 0

/-- Exact shifted higher-prime-power majorant, with the same strict finite
window support. -/
def gsA10HigherPrimePowerLambdaWindowWeight
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (y X : ℕ) (rho : ℝ) (n : ℕ) : ℝ :=
  if y < n ∧ n < X / y then
    ‖gsRealShift rho
      (gsHigherPrimePowerPart (gsA9HighGeneralizedMangoldt hmul y)) n‖
  else 0

/-- Source-sharp ordinary majorant for one shifted generalized-Mangoldt
window: exact prime-only high support plus the HPP correction. -/
def gsA10OrdinaryLambdaNearWeight
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (y X : ℕ) (rho : ℝ) (n : ℕ) : ℝ :=
  gsA10ShiftedPrimeLambdaWindowWeight y X rho n +
    gsA10HigherPrimePowerLambdaWindowWeight hmul y X rho n

theorem gsA10ShiftedPrimeLambdaWindowWeight_nonneg
    (y X : ℕ) (rho : ℝ) (n : ℕ) :
    0 ≤ gsA10ShiftedPrimeLambdaWindowWeight y X rho n := by
  unfold gsA10ShiftedPrimeLambdaWindowWeight
  split_ifs
  · exact mul_nonneg (Real.exp_nonneg _)
      ArithmeticFunction.vonMangoldt_nonneg
  · norm_num
  · norm_num

theorem gsA10HigherPrimePowerLambdaWindowWeight_nonneg
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (y X : ℕ) (rho : ℝ) (n : ℕ) :
    0 ≤ gsA10HigherPrimePowerLambdaWindowWeight hmul y X rho n := by
  unfold gsA10HigherPrimePowerLambdaWindowWeight
  split_ifs
  · exact norm_nonneg _
  · exact le_rfl

theorem gsA10OrdinaryLambdaNearWeight_nonneg
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (y X : ℕ) (rho : ℝ) (n : ℕ) :
    0 ≤ gsA10OrdinaryLambdaNearWeight hmul y X rho n := by
  unfold gsA10OrdinaryLambdaNearWeight
  exact add_nonneg
    (gsA10ShiftedPrimeLambdaWindowWeight_nonneg y X rho n)
    (gsA10HigherPrimePowerLambdaWindowWeight_nonneg hmul y X rho n)

/-- Exact prime/HPP majorization of a finite shifted Lambda window.  No
complete multiplicativity is used. -/
theorem norm_gsRealShift_gsA10LambdaWindow_le_ordinaryNearWeight
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (y X : ℕ) {rho : ℝ} (_hrho : 0 ≤ rho) (n : ℕ) :
    ‖gsRealShift rho
        (gsA10LambdaWindow (gsA9HighGeneralizedMangoldt hmul y) y X) n‖ ≤
      gsA10OrdinaryLambdaNearWeight hmul y X rho n := by
  let lambda : ArithmeticFunction ℂ := gsA9HighGeneralizedMangoldt hmul y
  let prime : ArithmeticFunction ℂ := gsPrimePart lambda
  let hpp : ArithmeticFunction ℂ := gsHigherPrimePowerPart lambda
  have hlambda : lambda = prime + hpp :=
    gsA9HighGeneralizedMangoldt_eq_primePart_add_higherPrimePowerPart hmul y
  by_cases hn : n = 0
  · subst n
    simp [gsA10OrdinaryLambdaNearWeight,
      gsA10ShiftedPrimeLambdaWindowWeight,
      gsA10HigherPrimePowerLambdaWindowWeight]
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  rw [gsRealShift_apply_of_ne_zero rho _ hn]
  rw [gsA10LambdaWindow_apply]
  split_ifs with hwin
  · have hpoint : lambda n = prime n + hpp n := by
      simpa only [ArithmeticFunction.add_apply] using
        DFunLike.congr_fun hlambda n
    rw [hpoint, mul_add]
    have hprime : ‖prime n‖ ≤
        if n.Prime then ArithmeticFunction.vonMangoldt n else 0 := by
      by_cases hp : n.Prime
      · rw [if_pos hp]
        simpa only [prime, lambda] using
          (norm_gsPrimePart_highGeneralizedMangoldt_le_vonMangoldt
            hmul hbound y n)
      · rw [if_neg hp, gsPrimePart_apply, if_neg hp, norm_zero]
    have hprimeShift :
        ‖(Real.exp (-rho * Real.log (n : ℝ)) : ℂ) * prime n‖ ≤
          Real.exp (-rho * Real.log (n : ℝ)) *
            (if n.Prime then ArithmeticFunction.vonMangoldt n else 0) := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.exp_nonneg _)]
      exact mul_le_mul_of_nonneg_left hprime (Real.exp_nonneg _)
    calc
      ‖(Real.exp (-rho * Real.log (n : ℝ)) : ℂ) * prime n +
          (Real.exp (-rho * Real.log (n : ℝ)) : ℂ) * hpp n‖ ≤
          ‖(Real.exp (-rho * Real.log (n : ℝ)) : ℂ) * prime n‖ +
            ‖(Real.exp (-rho * Real.log (n : ℝ)) : ℂ) * hpp n‖ :=
        norm_add_le _ _
      _ ≤ Real.exp (-rho * Real.log (n : ℝ)) *
            (if n.Prime then ArithmeticFunction.vonMangoldt n else 0) +
            ‖gsRealShift rho hpp n‖ := by
        rw [gsRealShift_apply_of_ne_zero rho hpp hn]
        exact add_le_add hprimeShift le_rfl
      _ = gsA10OrdinaryLambdaNearWeight hmul y X rho n := by
        unfold gsA10OrdinaryLambdaNearWeight
          gsA10ShiftedPrimeLambdaWindowWeight
          gsA10HigherPrimePowerLambdaWindowWeight
        rw [if_pos hwin, if_pos hwin]
  · rw [mul_zero, norm_zero]
    exact gsA10OrdinaryLambdaNearWeight_nonneg hmul y X rho n

/-- The higher-prime-power correction in the ordinary near weight has the
same reciprocal-mass bound as in the source secondary estimate. -/
theorem sum_gsA10HigherPrimePowerLambdaWindowWeight_div_le_mass
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {y X K : ℕ} {rho : ℝ} (hrho : 0 ≤ rho) :
    (∑ n ∈ Finset.Icc 1 K,
        gsA10HigherPrimePowerLambdaWindowWeight hmul y X rho n /
          (n : ℝ)) ≤
      gsA10HigherPrimePowerGeometricMass y K := by
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 K,
        ‖gsRealShift rho
          (gsHigherPrimePowerPart
            (gsA9HighGeneralizedMangoldt hmul y)) n‖ / (n : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      unfold gsA10HigherPrimePowerLambdaWindowWeight
      split_ifs
      · exact le_rfl
      · simpa only [zero_div] using
          (div_nonneg
            (norm_nonneg
              (gsRealShift rho
                (gsHigherPrimePowerPart
                  (gsA9HighGeneralizedMangoldt hmul y)) n))
            (Nat.cast_nonneg n))
    _ ≤ gsA10HigherPrimePowerGeometricMass y K :=
      sum_norm_shift_higherPrimePowerPart_div_le_mass
        hmul hbound (y := y) (X := K) (alpha := rho) hrho

/-- A convenient reciprocal-mass form for the full ordinary near weight. -/
theorem sum_gsA10OrdinaryLambdaNearWeight_div_le_prime_add_mass
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {y X K : ℕ} {rho : ℝ} (hrho : 0 ≤ rho) :
    (∑ n ∈ Finset.Icc 1 K,
        gsA10OrdinaryLambdaNearWeight hmul y X rho n / (n : ℝ)) ≤
      (∑ n ∈ Finset.Icc 1 K,
        gsA10ShiftedPrimeLambdaWindowWeight y X rho n / (n : ℝ)) +
          gsA10HigherPrimePowerGeometricMass y K := by
  have hhpp := sum_gsA10HigherPrimePowerLambdaWindowWeight_div_le_mass
    hmul hbound (y := y) (X := X) (K := K) (rho := rho) hrho
  simp_rw [gsA10OrdinaryLambdaNearWeight, add_div]
  rw [Finset.sum_add_distrib]
  exact add_le_add le_rfl hhpp

/-- Ordinary-multiplicative replacement for the complete-multiplicative
near-mass theorem.  The exact nonnegative weights `B` and `C` retain the
higher-prime-power corrections; their reciprocal corrections are bounded
by `gsA10HigherPrimePowerGeometricMass` above. -/
theorem dirichletPerronNearMass_gsA10TwoBlockTailoredCoefficient_le_ordinary
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂]
    {y X : ℕ}
    (hQ₂ : ∀ p, (¬ P₁ p ∧ P₂ p) → p ≤ y)
    (hQ₃ : ∀ p, (¬ P₁ p ∧ ¬ P₂ p) → p ≤ y)
    (hX : 0 < X) {T : ℝ} (hT : 0 < T)
    {alpha beta : ℝ} (halpha : 0 ≤ alpha) (hbeta : 0 ≤ beta) :
    dirichletPerronNearMass
        (gsA10TwoBlockTailoredCoefficient
          f hmul P₁ P₂ y X alpha beta) X T ≤
      ∑ a ∈ gsPositiveBelow (2 * X + 1),
        ∑ b ∈ (gsPositiveBelow (2 * X + 1)).filter
            (fun b ↦ a * b < 2 * X + 1),
          gsA10OrdinaryLambdaNearWeight hmul y X alpha a *
            gsA10OrdinaryLambdaNearWeight hmul y X (alpha + 2 * beta) b *
              (2 + (4 * (X : ℝ) / T) * ((a * b : ℕ) : ℝ)⁻¹ *
                (harmonic (2 * X) : ℝ)) := by
  let base : ArithmeticFunction ℂ :=
    gsA10TwoBlockAlternatingLow f P₁ P₂ y *
      gsRealShift (alpha + 2 * beta) (gsA9HighArithmetic f y)
  let W₁ : ArithmeticFunction ℂ :=
    gsRealShift alpha
      (gsA10LambdaWindow (gsA9HighGeneralizedMangoldt hmul y) y X)
  let W₂ : ArithmeticFunction ℂ :=
    gsRealShift (alpha + 2 * beta)
      (gsA10LambdaWindow (gsA9HighGeneralizedMangoldt hmul y) y X)
  let B : ℕ → ℝ := gsA10OrdinaryLambdaNearWeight hmul y X alpha
  let C : ℕ → ℝ :=
    gsA10OrdinaryLambdaNearWeight hmul y X (alpha + 2 * beta)
  have hbase : ∀ n, ‖base n‖ ≤ (1 : ℝ) := by
    intro n
    exact norm_gsA10TwoBlockLowHighShift_le_one_ordinaryNear
      hmul hbound P₁ P₂ y
      hQ₂ hQ₃ (by linarith) n
  have hW₁ : ∀ n, ‖W₁ n‖ ≤ B n := by
    intro n
    exact norm_gsRealShift_gsA10LambdaWindow_le_ordinaryNearWeight
      hmul hbound y X halpha n
  have hW₂ : ∀ n, ‖W₂ n‖ ≤ C n := by
    intro n
    exact norm_gsRealShift_gsA10LambdaWindow_le_ordinaryNearWeight
      hmul hbound y X (by linarith) n
  have hgeneric := dirichletPerronNearMass_mul_mul_le hX hT
    base W₁ W₂ (fun _ ↦ (1 : ℝ)) B C
    hbase hW₁ hW₂ (fun _ ↦ by norm_num) (fun _ ↦ by norm_num)
    (fun n ↦ gsA10OrdinaryLambdaNearWeight_nonneg hmul y X alpha n)
    (fun n ↦ gsA10OrdinaryLambdaNearWeight_nonneg
      hmul y X (alpha + 2 * beta) n)
  have hcoeff :
      gsA10TwoBlockTailoredCoefficient f hmul P₁ P₂ y X alpha beta =
        (W₁ * W₂) * base := by
    dsimp only [gsA10TwoBlockTailoredCoefficient, gsA10TailoredCoefficient,
      base, W₁, W₂]
    rw [mul_comm]
  rw [hcoeff]
  simpa only [B, C] using hgeneric

end

end Erdos67b.MRHalaszBands

#print axioms Erdos67b.MRHalaszBands.norm_gsRealShift_gsA10LambdaWindow_le_ordinaryNearWeight
#print axioms Erdos67b.MRHalaszBands.sum_gsA10HigherPrimePowerLambdaWindowWeight_div_le_mass
#print axioms Erdos67b.MRHalaszBands.dirichletPerronNearMass_gsA10TwoBlockTailoredCoefficient_le_ordinary
