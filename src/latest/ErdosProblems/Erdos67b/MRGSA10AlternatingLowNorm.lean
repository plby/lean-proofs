import ErdosProblems.Erdos67b.MRGSA10SecondaryCoefficientMajorant

/-!
# The two-block alternating low coefficient is one-bounded

On integers supported on primes at most `y`, the alternating low coefficient
from the A.10 reconstruction is exactly the original two-block typical
coefficient.  The proof keeps the alternating coefficient intact: after
convolution with the complementary high coefficient, unique low/high prime
factorization says that only the divisor pair `(n, 1)` contributes.

This is the support estimate needed to count the higher-prime-power part of
the second A.10 secondary term without expanding the alternating coefficient
into four deletion terms.
-/

namespace Erdos67b.MRHalaszBands

noncomputable section

/-- On its low-prime support, the A.10 alternating low coefficient is the
two-block typical coefficient. -/
theorem gsA10TwoBlockAlternatingLow_eq_typical_of_lowSupported
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂]
    (y : ℕ) {n : ℕ} (hn : 0 < n)
    (hQ₂ : ∀ p, (¬ P₁ p ∧ P₂ p) → p ≤ y)
    (hQ₃ : ∀ p, (¬ P₁ p ∧ ¬ P₂ p) → p ≤ y)
    (hnlow : PrimeSupported (fun p ↦ p ≤ y) n) :
    gsA10TwoBlockAlternatingLow f P₁ P₂ y n =
      finiteHalaszTypicalCoefficient f P₁ P₂ n := by
  let low := gsA10TwoBlockAlternatingLow f P₁ P₂ y
  let high := gsA9HighArithmetic f y
  have hparts := eq_primeBandParts_of_mul_eq (fun p ↦ p ≤ y)
    (show n * 1 = n by simp) hnlow
    (primeSupported_one (fun p ↦ ¬ p ≤ y))
  have hprod : (low * high) n = low n := by
    rw [ArithmeticFunction.mul_apply]
    rw [Finset.sum_eq_single (n, 1)]
    · simp [low, high, gsA9HighArithmetic_one hmul y]
    · intro q hq hqne
      have hq1 : q.1 ≠ 0 :=
        (Nat.ne_zero_of_mem_divisorsAntidiagonal hq).1
      have hq2 : q.2 ≠ 0 :=
        (Nat.ne_zero_of_mem_divisorsAntidiagonal hq).2
      by_cases hlow : PrimeSupported (fun p ↦ p ≤ y) q.1
      · by_cases hhigh : PrimeSupported (fun p ↦ ¬ p ≤ y) q.2
        · have hu := eq_primeBandParts_of_mul_eq (fun p ↦ p ≤ y)
            (Nat.mem_divisorsAntidiagonal.mp hq).1 hlow hhigh
          have hqn : q.1 = n := hu.1.trans hparts.1.symm
          have hqone : q.2 = 1 := hu.2.trans hparts.2.symm
          exact (hqne (Prod.ext hqn hqone)).elim
        · rw [gsA9HighArithmetic_apply_of_ne_zero f y hq2]
          unfold gsA9High primeBandCoefficient
          rw [if_neg hhigh, mul_zero]
      · rw [gsA10TwoBlockAlternatingLow_eq_zero_of_not_lowSupported
            f P₁ P₂ y hq1 hlow, zero_mul]
    · intro hnot
      exact (hnot (Nat.mem_divisorsAntidiagonal.mpr
        ⟨by simp, hn.ne'⟩)).elim
  have hrec := congrFun (congrArg DFunLike.coe
    (gsA10TwoBlockAlternatingLow_mul_high_eq_typical
      hmul P₁ P₂ y hQ₂ hQ₃)) n
  change low n = finiteHalaszTypicalCoefficient f P₁ P₂ n
  rw [← hprod]
  simpa [toArithmeticFunction, hn.ne'] using hrec

/-- The whole alternating low coefficient is one-bounded on its natural
low-prime support. -/
theorem norm_gsA10TwoBlockAlternatingLow_le_one_of_lowSupported
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂]
    (y : ℕ) {n : ℕ} (hn : 0 < n)
    (hQ₂ : ∀ p, (¬ P₁ p ∧ P₂ p) → p ≤ y)
    (hQ₃ : ∀ p, (¬ P₁ p ∧ ¬ P₂ p) → p ≤ y)
    (hnlow : PrimeSupported (fun p ↦ p ≤ y) n) :
    ‖gsA10TwoBlockAlternatingLow f P₁ P₂ y n‖ ≤ 1 := by
  rw [gsA10TwoBlockAlternatingLow_eq_typical_of_lowSupported
    hmul P₁ P₂ y hn hQ₂ hQ₃ hnlow]
  unfold finiteHalaszTypicalCoefficient
  split
  · exact hbound _ hn
  · simp

end

end Erdos67b.MRHalaszBands
