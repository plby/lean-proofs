import ErdosProblems.Erdos67b.MRGSA10TailoredNearMassOrdinary
import ErdosProblems.Erdos67b.MRGSA10TailoredNearMass

/-!
# Ordinary-multiplicative half-endpoint error in the A.10 Perron formula

The half-jump in the finite Perron formula is a single coefficient, not a
vertical coefficient mass.  For an ordinary multiplicative function its two
generalized-Mangoldt factors are split into their exact prime parts and their
higher-prime-power corrections.  The prime--prime contribution retains the
classical `log(X)^2` pointwise bound.  All failure of the completely
multiplicative estimate is isolated in one explicit, nonnegative divisor
remainder with the strict source window still present.
-/

open scoped BigOperators
open Finset

namespace Erdos67b.MRHalaszBands

noncomputable section

open BoundedGaps.Maynard
open MRPerronNearTripleConvolution

/-- The exact higher-prime-power correction left in the A.10 endpoint
coefficient after the prime--prime term has been separated. -/
def gsA10OrdinaryHalfEndpointHPPError
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (y X : ℕ) (alpha beta : ℝ) : ℝ :=
  ∑ uv ∈ X.divisorsAntidiagonal,
    ∑ ab ∈ uv.1.divisorsAntidiagonal,
      (gsA10ShiftedPrimeLambdaWindowWeight y X alpha ab.1 *
          gsA10HigherPrimePowerLambdaWindowWeight hmul y X
            (alpha + 2 * beta) ab.2 +
        gsA10HigherPrimePowerLambdaWindowWeight hmul y X alpha ab.1 *
          gsA10ShiftedPrimeLambdaWindowWeight y X
            (alpha + 2 * beta) ab.2 +
        gsA10HigherPrimePowerLambdaWindowWeight hmul y X alpha ab.1 *
          gsA10HigherPrimePowerLambdaWindowWeight hmul y X
            (alpha + 2 * beta) ab.2)

theorem gsA10OrdinaryHalfEndpointHPPError_nonneg
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (y X : ℕ) (alpha beta : ℝ) :
    0 ≤ gsA10OrdinaryHalfEndpointHPPError hmul y X alpha beta := by
  unfold gsA10OrdinaryHalfEndpointHPPError
  apply Finset.sum_nonneg
  intro uv huv
  apply Finset.sum_nonneg
  intro ab hab
  exact add_nonneg
    (add_nonneg
      (mul_nonneg
        (gsA10ShiftedPrimeLambdaWindowWeight_nonneg y X alpha ab.1)
        (gsA10HigherPrimePowerLambdaWindowWeight_nonneg
          hmul y X (alpha + 2 * beta) ab.2))
      (mul_nonneg
        (gsA10HigherPrimePowerLambdaWindowWeight_nonneg
          hmul y X alpha ab.1)
        (gsA10ShiftedPrimeLambdaWindowWeight_nonneg
          y X (alpha + 2 * beta) ab.2)))
    (mul_nonneg
      (gsA10HigherPrimePowerLambdaWindowWeight_nonneg
        hmul y X alpha ab.1)
      (gsA10HigherPrimePowerLambdaWindowWeight_nonneg
        hmul y X (alpha + 2 * beta) ab.2))

private theorem shiftedPrimeLambdaWindowWeight_le_vonMangoldt
    (y X : ℕ) {rho : ℝ} (hrho : 0 ≤ rho) (n : ℕ) :
    gsA10ShiftedPrimeLambdaWindowWeight y X rho n ≤
      ArithmeticFunction.vonMangoldt n := by
  unfold gsA10ShiftedPrimeLambdaWindowWeight
  split_ifs with hwin hp
  · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hp.one_le
    have hexp : Real.exp (-rho * Real.log (n : ℝ)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      rw [neg_mul]
      exact neg_nonpos.mpr (mul_nonneg hrho (Real.log_nonneg hn1))
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hexp
      (ArithmeticFunction.vonMangoldt_nonneg (n := n))
  · rw [mul_zero]
    exact ArithmeticFunction.vonMangoldt_nonneg
  · exact ArithmeticFunction.vonMangoldt_nonneg

private theorem shiftedPrimeLambdaWindowWeight_le_zeroShift
    (y X : ℕ) {rho : ℝ} (hrho : 0 ≤ rho) (n : ℕ) :
    gsA10ShiftedPrimeLambdaWindowWeight y X rho n ≤
      gsA10ShiftedPrimeLambdaWindowWeight y X 0 n := by
  unfold gsA10ShiftedPrimeLambdaWindowWeight
  split_ifs with hwin hp
  · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hp.one_le
    have hexp : Real.exp (-rho * Real.log (n : ℝ)) ≤ 1 := by
      rw [Real.exp_le_one_iff, neg_mul]
      exact neg_nonpos.mpr (mul_nonneg hrho (Real.log_nonneg hn1))
    simpa only [zero_mul, neg_zero, Real.exp_zero, one_mul] using
      mul_le_mul_of_nonneg_right hexp
        (ArithmeticFunction.vonMangoldt_nonneg (n := n))
  · simp
  · simp

private theorem higherPrimePowerLambdaWindowWeight_le_zeroShift
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (y X : ℕ) {rho : ℝ} (hrho : 0 ≤ rho) (n : ℕ) :
    gsA10HigherPrimePowerLambdaWindowWeight hmul y X rho n ≤
      gsA10HigherPrimePowerLambdaWindowWeight hmul y X 0 n := by
  unfold gsA10HigherPrimePowerLambdaWindowWeight
  split_ifs with hwin
  · have hnpos : 0 < n := lt_of_le_of_lt (Nat.zero_le y) hwin.1
    have hn0 : n ≠ 0 := Nat.ne_of_gt hnpos
    have hn1 : (1 : ℝ) ≤ n := by
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn0)
    have hexp : Real.exp (-rho * Real.log (n : ℝ)) ≤ 1 := by
      rw [Real.exp_le_one_iff, neg_mul]
      exact neg_nonpos.mpr (mul_nonneg hrho (Real.log_nonneg hn1))
    rw [gsRealShift_apply_of_ne_zero rho _ hn0,
      gsRealShift_apply_of_ne_zero 0 _ hn0, norm_mul, norm_mul,
      Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
    simp only [zero_mul, neg_zero, Real.exp_zero, abs_one, one_mul]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hexp
      (norm_nonneg
        ((gsHigherPrimePowerPart
          (gsA9HighGeneralizedMangoldt hmul y)) n))
  · exact le_rfl

/-- The explicit HPP endpoint remainder is largest at zero shift.  This
makes it a constant envelope on the whole nonnegative alpha--beta
rectangle. -/
theorem gsA10OrdinaryHalfEndpointHPPError_le_zero
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (y X : ℕ) {alpha beta : ℝ}
    (halpha : 0 ≤ alpha) (hbeta : 0 ≤ beta) :
    gsA10OrdinaryHalfEndpointHPPError hmul y X alpha beta ≤
      gsA10OrdinaryHalfEndpointHPPError hmul y X 0 0 := by
  unfold gsA10OrdinaryHalfEndpointHPPError
  apply Finset.sum_le_sum
  intro uv huv
  apply Finset.sum_le_sum
  intro ab hab
  have hrho : 0 ≤ alpha + 2 * beta := by linarith
  have hP₁ := shiftedPrimeLambdaWindowWeight_le_zeroShift
    y X halpha ab.1
  have hP₂ := shiftedPrimeLambdaWindowWeight_le_zeroShift
    y X hrho ab.2
  have hH₁ := higherPrimePowerLambdaWindowWeight_le_zeroShift
    hmul y X halpha ab.1
  have hH₂ := higherPrimePowerLambdaWindowWeight_le_zeroShift
    hmul y X hrho ab.2
  have hP₁0 := gsA10ShiftedPrimeLambdaWindowWeight_nonneg
    y X alpha ab.1
  have hP₂0 := gsA10ShiftedPrimeLambdaWindowWeight_nonneg
    y X (alpha + 2 * beta) ab.2
  have hH₁0 := gsA10HigherPrimePowerLambdaWindowWeight_nonneg
    hmul y X alpha ab.1
  have hH₂0 := gsA10HigherPrimePowerLambdaWindowWeight_nonneg
    hmul y X (alpha + 2 * beta) ab.2
  have hP₁z0 := gsA10ShiftedPrimeLambdaWindowWeight_nonneg
    y X 0 ab.1
  have hP₂z0 := gsA10ShiftedPrimeLambdaWindowWeight_nonneg
    y X 0 ab.2
  have hH₁z0 := gsA10HigherPrimePowerLambdaWindowWeight_nonneg
    hmul y X 0 ab.1
  have hH₂z0 := gsA10HigherPrimePowerLambdaWindowWeight_nonneg
    hmul y X 0 ab.2
  simpa only [zero_add, mul_zero] using add_le_add
    (add_le_add
      (mul_le_mul hP₁ hH₂ hH₂0 hP₁z0)
      (mul_le_mul hH₁ hP₂ hP₂0 hH₁z0))
    (mul_le_mul hH₁ hH₂ hH₂0 hH₁z0)

/-- Ordinary-multiplicative pointwise endpoint bound.  The main
prime--prime contribution is exactly the same `log(X)^2` term as in the
completely multiplicative case; the explicit final summand contains every
higher-prime-power correction. -/
theorem norm_gsA10TwoBlockTailoredCoefficient_apply_le_log_sq_add_hpp
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂]
    {y X : ℕ}
    (hQ₂ : ∀ p, (¬ P₁ p ∧ P₂ p) → p ≤ y)
    (hQ₃ : ∀ p, (¬ P₁ p ∧ ¬ P₂ p) → p ≤ y)
    (hX : 0 < X) {alpha beta : ℝ}
    (halpha : 0 ≤ alpha) (hbeta : 0 ≤ beta) :
    ‖gsA10TwoBlockTailoredCoefficient
        f hmul P₁ P₂ y X alpha beta X‖ ≤
      (Real.log (X : ℝ)) ^ 2 +
        gsA10OrdinaryHalfEndpointHPPError hmul y X alpha beta := by
  let base : ArithmeticFunction ℂ :=
    gsA10TwoBlockAlternatingLow f P₁ P₂ y *
      gsRealShift (alpha + 2 * beta) (gsA9HighArithmetic f y)
  let W₁ : ArithmeticFunction ℂ :=
    gsRealShift alpha
      (gsA10LambdaWindow (gsA9HighGeneralizedMangoldt hmul y) y X)
  let W₂ : ArithmeticFunction ℂ :=
    gsRealShift (alpha + 2 * beta)
      (gsA10LambdaWindow (gsA9HighGeneralizedMangoldt hmul y) y X)
  let P : ℕ → ℝ := gsA10ShiftedPrimeLambdaWindowWeight y X alpha
  let Q : ℕ → ℝ :=
    gsA10ShiftedPrimeLambdaWindowWeight y X (alpha + 2 * beta)
  let H : ℕ → ℝ :=
    gsA10HigherPrimePowerLambdaWindowWeight hmul y X alpha
  let K : ℕ → ℝ :=
    gsA10HigherPrimePowerLambdaWindowWeight hmul y X (alpha + 2 * beta)
  have hbase : ∀ n, ‖base n‖ ≤ (1 : ℝ) := by
    intro n
    exact norm_gsA10TwoBlockLowHighShift_le_one
      hmul hbound P₁ P₂ y hQ₂ hQ₃ (by linarith) n
  have hW₁ : ∀ n, ‖W₁ n‖ ≤ P n + H n := by
    intro n
    simpa only [W₁, P, H, gsA10OrdinaryLambdaNearWeight] using
      (norm_gsRealShift_gsA10LambdaWindow_le_ordinaryNearWeight
        hmul hbound y X halpha n)
  have hW₂ : ∀ n, ‖W₂ n‖ ≤ Q n + K n := by
    intro n
    simpa only [W₂, Q, K, gsA10OrdinaryLambdaNearWeight] using
      (norm_gsRealShift_gsA10LambdaWindow_le_ordinaryNearWeight
        hmul hbound y X (by linarith) n)
  have hP0 : ∀ n, 0 ≤ P n := fun n ↦
    gsA10ShiftedPrimeLambdaWindowWeight_nonneg y X alpha n
  have hQ0 : ∀ n, 0 ≤ Q n := fun n ↦
    gsA10ShiftedPrimeLambdaWindowWeight_nonneg y X
      (alpha + 2 * beta) n
  have hH0 : ∀ n, 0 ≤ H n := fun n ↦
    gsA10HigherPrimePowerLambdaWindowWeight_nonneg hmul y X alpha n
  have hK0 : ∀ n, 0 ≤ K n := fun n ↦
    gsA10HigherPrimePowerLambdaWindowWeight_nonneg hmul y X
      (alpha + 2 * beta) n
  have hcoeff :
      gsA10TwoBlockTailoredCoefficient f hmul P₁ P₂ y X alpha beta =
        (W₁ * W₂) * base := by
    dsimp only [gsA10TwoBlockTailoredCoefficient, gsA10TailoredCoefficient,
      base, W₁, W₂]
    rw [mul_comm]
  rw [hcoeff]
  have hraw := norm_mul_mul_apply_le_nested base W₁ W₂
    (fun _ ↦ (1 : ℝ)) (fun n ↦ P n + H n) (fun n ↦ Q n + K n)
    hbase hW₁ hW₂ (fun _ ↦ by norm_num)
    (fun n ↦ add_nonneg (hP0 n) (hH0 n))
    (fun n ↦ add_nonneg (hQ0 n) (hK0 n)) X
  refine hraw.trans ?_
  have hP : ∀ n, P n ≤ ArithmeticFunction.vonMangoldt n := fun n ↦
    shiftedPrimeLambdaWindowWeight_le_vonMangoldt y X halpha n
  have hQ : ∀ n, Q n ≤ ArithmeticFunction.vonMangoldt n := fun n ↦
    shiftedPrimeLambdaWindowWeight_le_vonMangoldt y X (by linarith) n
  calc
    (∑ uv ∈ X.divisorsAntidiagonal,
      ∑ ab ∈ uv.1.divisorsAntidiagonal,
        (1 : ℝ) * (P ab.1 + H ab.1) * (Q ab.2 + K ab.2)) =
        (∑ uv ∈ X.divisorsAntidiagonal,
          ∑ ab ∈ uv.1.divisorsAntidiagonal,
            P ab.1 * Q ab.2) +
          gsA10OrdinaryHalfEndpointHPPError hmul y X alpha beta := by
      unfold gsA10OrdinaryHalfEndpointHPPError
      simp only [P, Q, H, K, one_mul]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro uv huv
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro ab hab
      ring
    _ ≤ (∑ uv ∈ X.divisorsAntidiagonal,
          ∑ ab ∈ uv.1.divisorsAntidiagonal,
            ArithmeticFunction.vonMangoldt ab.1 *
              ArithmeticFunction.vonMangoldt ab.2) +
          gsA10OrdinaryHalfEndpointHPPError hmul y X alpha beta := by
      exact add_le_add
        (Finset.sum_le_sum fun uv huv ↦
          Finset.sum_le_sum fun ab hab ↦
            mul_le_mul (hP ab.1) (hQ ab.2)
              (hQ0 ab.2) ArithmeticFunction.vonMangoldt_nonneg)
        le_rfl
    _ ≤ (Real.log (X : ℝ)) ^ 2 +
          gsA10OrdinaryHalfEndpointHPPError hmul y X alpha beta :=
      add_le_add (sum_nested_vonMangoldt_le_log_sq hX) le_rfl

/-- Normalized half-jump form used after dividing the A.10 prefix by its
length.  The prime contribution is `log(X)^2/(2X)`; the only remaining
ordinary-multiplicative term is the explicit HPP divisor correction. -/
theorem norm_gsA10TwoBlockTailoredCoefficient_div_two_mul_le
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂]
    {y X : ℕ}
    (hQ₂ : ∀ p, (¬ P₁ p ∧ P₂ p) → p ≤ y)
    (hQ₃ : ∀ p, (¬ P₁ p ∧ ¬ P₂ p) → p ≤ y)
    (hX : 0 < X) {alpha beta : ℝ}
    (halpha : 0 ≤ alpha) (hbeta : 0 ≤ beta) :
    ‖gsA10TwoBlockTailoredCoefficient
        f hmul P₁ P₂ y X alpha beta X‖ / (2 * (X : ℝ)) ≤
      ((Real.log (X : ℝ)) ^ 2 +
        gsA10OrdinaryHalfEndpointHPPError hmul y X alpha beta) /
          (2 * (X : ℝ)) := by
  exact div_le_div_of_nonneg_right
    (norm_gsA10TwoBlockTailoredCoefficient_apply_le_log_sq_add_hpp
      hmul hbound P₁ P₂ hQ₂ hQ₃ hX halpha hbeta)
    (by positivity)

/-- Alpha--beta independent normalized half-jump envelope. -/
theorem norm_gsA10TwoBlockTailoredCoefficient_div_two_mul_le_zeroHPP
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂]
    {y X : ℕ}
    (hQ₂ : ∀ p, (¬ P₁ p ∧ P₂ p) → p ≤ y)
    (hQ₃ : ∀ p, (¬ P₁ p ∧ ¬ P₂ p) → p ≤ y)
    (hX : 0 < X) {alpha beta : ℝ}
    (halpha : 0 ≤ alpha) (hbeta : 0 ≤ beta) :
    ‖gsA10TwoBlockTailoredCoefficient
        f hmul P₁ P₂ y X alpha beta X‖ / (2 * (X : ℝ)) ≤
      ((Real.log (X : ℝ)) ^ 2 +
        gsA10OrdinaryHalfEndpointHPPError hmul y X 0 0) /
          (2 * (X : ℝ)) := by
  refine (norm_gsA10TwoBlockTailoredCoefficient_div_two_mul_le
    hmul hbound P₁ P₂ hQ₂ hQ₃ hX halpha hbeta).trans ?_
  apply div_le_div_of_nonneg_right
  exact add_le_add le_rfl
    (gsA10OrdinaryHalfEndpointHPPError_le_zero
      hmul y X halpha hbeta)
  positivity

end

end Erdos67b.MRHalaszBands

#print axioms
  Erdos67b.MRHalaszBands.norm_gsA10TwoBlockTailoredCoefficient_apply_le_log_sq_add_hpp
#print axioms
  Erdos67b.MRHalaszBands.norm_gsA10TwoBlockTailoredCoefficient_div_two_mul_le
#print axioms
  Erdos67b.MRHalaszBands.norm_gsA10TwoBlockTailoredCoefficient_div_two_mul_le_zeroHPP
