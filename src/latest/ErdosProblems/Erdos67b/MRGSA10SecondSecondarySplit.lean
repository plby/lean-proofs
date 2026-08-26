import ErdosProblems.Erdos67b.MRGSA10GeneralizedMangoldtSplit
import ErdosProblems.Erdos67b.MRGSA10GlobalSecondary

/-!
# Prime/higher-prime-power split of the second A.10 secondary term

The generalized Mangoldt coefficient of a merely multiplicative function
is split into its exact prime part and its higher-prime-power remainder
before either term is estimated.  This file proves that the finite prefix
and the auxiliary interval integral preserve that split exactly.
-/

namespace Erdos67b.MRHalaszBands

noncomputable section

private theorem gsRealShift_add_coeff (rho : ℝ)
    (a b : ArithmeticFunction ℂ) :
    gsRealShift rho (a + b) = gsRealShift rho a + gsRealShift rho b := by
  ext n
  by_cases hn : n = 0
  · subst n
    simp
  simp [gsRealShift_apply_of_ne_zero, hn, mul_add]

private theorem positivePrefixSum_add_coeff
    (a b : ArithmeticFunction ℂ) (X : ℕ) :
    positivePrefixSum (fun n ↦ (a + b) n) X =
      positivePrefixSum (fun n ↦ a n) X +
        positivePrefixSum (fun n ↦ b n) X := by
  simp [positivePrefixSum, Finset.sum_add_distrib]

private theorem continuous_secondSecondaryIntegrand
    (low high lambda : ArithmeticFunction ℂ) (X : ℕ) (eta : ℝ) :
    Continuous (fun alpha : ℝ ↦
      positivePrefixSum
        (fun n ↦ ((low * gsRealShift alpha lambda) *
          gsRealShift (2 * eta + alpha) high) n) X) := by
  have hfun :
      (fun alpha : ℝ ↦
        positivePrefixSum
          (fun n ↦ ((low * gsRealShift alpha lambda) *
            gsRealShift (2 * eta + alpha) high) n) X) =
      (fun alpha : ℝ ↦ positivePrefixSum
        (fun n ↦ (low * gsRealShift alpha
          (lambda * gsRealShift (2 * eta) high)) n) X) := by
    funext alpha
    have hcoef :
        (low * gsRealShift alpha lambda) *
            gsRealShift (2 * eta + alpha) high =
          low * gsRealShift alpha
            (lambda * gsRealShift (2 * eta) high) := by
      rw [show 2 * eta + alpha = alpha + 2 * eta by ring,
        ← gsRealShift_add alpha (2 * eta) high,
        mul_assoc, ← gsRealShift_mul]
    exact congrArg (fun c : ArithmeticFunction ℂ ↦
      positivePrefixSum (fun n ↦ c n) X) hcoef
  rw [hfun]
  exact continuous_positivePrefixSum_mul_gsRealShift
    low (lambda * gsRealShift (2 * eta) high) X

/-- The second A.10 secondary prefix is additive in its generalized
Mangoldt coefficient. -/
theorem gsA10SecondSecondaryPrefix_add
    (low high lambda₁ lambda₂ : ArithmeticFunction ℂ)
    (X : ℕ) (eta : ℝ) :
    gsA10SecondSecondaryPrefix low high (lambda₁ + lambda₂) X eta =
      gsA10SecondSecondaryPrefix low high lambda₁ X eta +
        gsA10SecondSecondaryPrefix low high lambda₂ X eta := by
  let F : ℝ → ℂ := fun alpha ↦ positivePrefixSum
    (fun n ↦ ((low * gsRealShift alpha lambda₁) *
      gsRealShift (2 * eta + alpha) high) n) X
  let G : ℝ → ℂ := fun alpha ↦ positivePrefixSum
    (fun n ↦ ((low * gsRealShift alpha lambda₂) *
      gsRealShift (2 * eta + alpha) high) n) X
  have hpoint : ∀ alpha,
      positivePrefixSum
        (fun n ↦ ((low * gsRealShift alpha (lambda₁ + lambda₂)) *
          gsRealShift (2 * eta + alpha) high) n) X =
        F alpha + G alpha := by
    intro alpha
    dsimp only [F, G]
    rw [gsRealShift_add_coeff]
    have hcoef :
        (low * (gsRealShift alpha lambda₁ + gsRealShift alpha lambda₂)) *
            gsRealShift (2 * eta + alpha) high =
          (low * gsRealShift alpha lambda₁) *
              gsRealShift (2 * eta + alpha) high +
            (low * gsRealShift alpha lambda₂) *
              gsRealShift (2 * eta + alpha) high := by ring
    rw [hcoef, positivePrefixSum_add_coeff]
  have hFcont : Continuous F := by
    exact continuous_secondSecondaryIntegrand low high lambda₁ X eta
  have hGcont : Continuous G := by
    exact continuous_secondSecondaryIntegrand low high lambda₂ X eta
  unfold gsA10SecondSecondaryPrefix
  rw [intervalIntegral.integral_congr (fun alpha _ ↦ hpoint alpha),
    intervalIntegral.integral_add
      (hFcont.intervalIntegrable _ _) (hGcont.intervalIntegrable _ _)]

/-- Exact prime/higher-prime-power split for the actual high generalized
Mangoldt coefficient in the two-block reconstruction. -/
theorem gsA10TwoBlockSecondSecondaryPrefix_eq_prime_add_higherPrimePower
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂]
    (y X : ℕ) (eta : ℝ) :
    gsA10SecondSecondaryPrefix
        (gsA10TwoBlockAlternatingLow f P₁ P₂ y)
        (gsA9HighArithmetic f y)
        (gsA9HighGeneralizedMangoldt hmul y) X eta =
      gsA10SecondSecondaryPrefix
          (gsA10TwoBlockAlternatingLow f P₁ P₂ y)
          (gsA9HighArithmetic f y)
          (gsPrimePart (gsA9HighGeneralizedMangoldt hmul y)) X eta +
        gsA10SecondSecondaryPrefix
          (gsA10TwoBlockAlternatingLow f P₁ P₂ y)
          (gsA9HighArithmetic f y)
          (gsHigherPrimePowerPart (gsA9HighGeneralizedMangoldt hmul y)) X eta := by
  let low := gsA10TwoBlockAlternatingLow f P₁ P₂ y
  let high := gsA9HighArithmetic f y
  let lambda := gsA9HighGeneralizedMangoldt hmul y
  let lambda₁ := gsPrimePart lambda
  let lambda₂ := gsHigherPrimePowerPart lambda
  have hsplit : lambda = lambda₁ + lambda₂ :=
    gsA9HighGeneralizedMangoldt_eq_primePart_add_higherPrimePowerPart hmul y
  change gsA10SecondSecondaryPrefix low high lambda X eta =
    gsA10SecondSecondaryPrefix low high lambda₁ X eta +
      gsA10SecondSecondaryPrefix low high lambda₂ X eta
  calc
    gsA10SecondSecondaryPrefix low high lambda X eta =
        gsA10SecondSecondaryPrefix low high (lambda₁ + lambda₂) X eta :=
      congrArg (fun u ↦ gsA10SecondSecondaryPrefix low high u X eta) hsplit
    _ = _ := gsA10SecondSecondaryPrefix_add low high lambda₁ lambda₂ X eta

end

end Erdos67b.MRHalaszBands
