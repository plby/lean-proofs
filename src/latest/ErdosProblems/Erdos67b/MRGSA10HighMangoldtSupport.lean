import ErdosProblems.Erdos67b.MRGSA10GeneralizedMangoldtSupport

/-!
# Support of the high-prime generalized Mangoldt coefficient

This specializes prime-power support to the common high factor in GS A.10.
In particular its generalized Mangoldt coefficient vanishes at every index
at most the low/high splitting point `y`, which is the exact fact needed to
replace the full coefficient by the finite Mangoldt window on prefixes of
length `X`.
-/

open scoped BigOperators

namespace Erdos67b.MRHalaszBands

noncomputable section

/-- The arithmetic wrapper of a prime-band coefficient is multiplicative. -/
theorem gsA9HighArithmetic_isMultiplicative
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f) (y : ℕ) :
    (gsA9HighArithmetic f y).IsMultiplicative := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  constructor
  · exact gsA9HighArithmetic_one hmul y
  · intro m n hm hn hcop
    rw [gsA9HighArithmetic_apply_of_ne_zero f y hm,
      gsA9HighArithmetic_apply_of_ne_zero f y hn,
      gsA9HighArithmetic_apply_of_ne_zero f y (mul_ne_zero hm hn)]
    exact (primeBandCoefficient_isMultiplicativeOnPositiveNat
      hmul (fun p ↦ ¬ p ≤ y)).2 m n (Nat.pos_of_ne_zero hm)
        (Nat.pos_of_ne_zero hn) hcop

/-- The high-prime arithmetic factor vanishes on every positive power of a
prime lying at or below the splitting point. -/
theorem gsA9HighArithmetic_apply_prime_pow_eq_zero
    (f : ℕ → ℂ) (y : ℕ) {p k : ℕ}
    (hp : p.Prime) (hpy : p ≤ y) (hk : k ≠ 0) :
    gsA9HighArithmetic f y (p ^ k) = 0 := by
  rw [gsA9HighArithmetic_apply_of_ne_zero f y (pow_ne_zero _ hp.ne_zero)]
  unfold gsA9High primeBandCoefficient
  rw [if_neg]
  intro hsupp
  have hmem : p ∈ (p ^ k).primeFactors := by
    rw [Nat.primeFactors_pow p hk]
    exact hp.mem_primeFactors (dvd_refl p) hp.ne_zero
  exact (hsupp.2 p hmem) hpy

/-- If an arithmetic function vanishes on every positive power of a prime,
then so does its generalized Mangoldt coefficient at those powers. -/
theorem gsGeneralizedMangoldt_apply_prime_pow_eq_zero_of_self
    (a : ArithmeticFunction ℂ) (ha : Invertible (a 1))
    {p k : ℕ} (hp : p.Prime)
    (haPow : ∀ j : ℕ, j ≠ 0 → a (p ^ j) = 0) :
    gsGeneralizedMangoldt a ha (p ^ k) = 0 := by
  by_cases hk : k = 0
  · subst k
    exact gsGeneralizedMangoldt_one a ha
  unfold gsGeneralizedMangoldt
  rw [ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal (fun x y ↦
      gsLogWeighted a x * ArithmeticFunction.dirichletInverse a ha y),
    Nat.sum_divisors_prime_pow hp]
  apply Finset.sum_eq_zero
  intro j hj
  by_cases hj0 : j = 0
  · subst j
    simp [gsLogWeighted_apply]
  · rw [gsLogWeighted_apply, haPow j hj0]
    simp

/-- The actual high-factor generalized Mangoldt coefficient vanishes on
prime powers whose base prime belongs to the low range. -/
theorem gsA9HighGeneralizedMangoldt_apply_prime_pow_eq_zero
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (y : ℕ) {p k : ℕ} (hp : p.Prime) (hpy : p ≤ y) :
    gsA9HighGeneralizedMangoldt hmul y (p ^ k) = 0 := by
  apply gsGeneralizedMangoldt_apply_prime_pow_eq_zero_of_self
    (gsA9HighArithmetic f y) (gsA9HighArithmeticInvertible hmul y) hp
  intro j hj
  exact gsA9HighArithmetic_apply_prime_pow_eq_zero f y hp hpy hj

/-- Exact lower support of the A.10 generalized Mangoldt window: no
coefficient occurs at an index at most `y`. -/
theorem gsA9HighGeneralizedMangoldt_eq_zero_of_le
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (y : ℕ) {n : ℕ} (hn : n ≤ y) :
    gsA9HighGeneralizedMangoldt hmul y n = 0 := by
  by_cases hpp : IsPrimePow n
  · obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff _).mp hpp
    apply gsA9HighGeneralizedMangoldt_apply_prime_pow_eq_zero hmul y hp
    exact (Nat.le_self_pow hk.ne' p).trans hn
  · apply gsGeneralizedMangoldt_eq_zero_of_not_isPrimePow
      (gsA9HighArithmetic f y) (gsA9HighArithmeticInvertible hmul y)
      (gsA9HighArithmetic_isMultiplicative hmul y) hpp

end

end Erdos67b.MRHalaszBands
