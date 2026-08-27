import ErdosProblems.Erdos587.HooleyPrimeRecursion

/-!
# Exact harmonic divisor moments on squarefree products

The harmonic moments of the divisor count are finite Euler products.
This supplies the algebraic side of the estimates used in the Delta
moment induction. No prime-distribution estimate is assumed here.
-/

open scoped BigOperators

namespace Erdos587

noncomputable def divisorReciprocalPower (k : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun n => (n.divisors.card : ℝ) ^ k / n, by simp⟩

@[simp] lemma divisorReciprocalPower_apply (k n : ℕ) :
    divisorReciprocalPower k n = (n.divisors.card : ℝ) ^ k / n := rfl

lemma divisorReciprocalPower_isMultiplicative (k : ℕ) :
    (divisorReciprocalPower k).IsMultiplicative := by
  constructor
  · simp
  · intro m n hmn
    simp only [divisorReciprocalPower_apply, hmn.card_divisors_mul, Nat.cast_mul,
      mul_pow, mul_div_mul_comm]

lemma divisorReciprocalPower_prime (k : ℕ) {p : ℕ} (hp : p.Prime) :
    divisorReciprocalPower k p = 2 ^ k / (p : ℝ) := by
  have hcard := card_divisors_prime_mul hp
    (show ¬ p ∣ 1 from fun h => hp.ne_one (Nat.dvd_one.mp h))
  have hcard' : p.divisors.card = 2 := by simpa using hcard
  simp only [divisorReciprocalPower_apply, hcard', Nat.cast_ofNat]

/-- All positive squarefree divisors are included, without a cutoff on
their size; the finite prime support is the only restriction. -/
theorem sum_divisorReciprocalPower_eq_eulerProduct (k : ℕ) {n : ℕ}
    (hn : Squarefree n) :
    (∑ d ∈ n.divisors, (d.divisors.card : ℝ) ^ k / d) =
      ∏ p ∈ n.primeFactors, (1 + 2 ^ k / (p : ℝ)) := by
  change (∑ d ∈ n.divisors, divisorReciprocalPower k d) = _
  rw [← (divisorReciprocalPower_isMultiplicative k).prodPrimeFactors_one_add_of_squarefree hn]
  apply Finset.prod_congr rfl
  intro p hp
  rw [divisorReciprocalPower_prime k (Nat.prime_of_mem_primeFactors hp)]

theorem sum_reciprocal_divisors_eq_eulerProduct {n : ℕ} (hn : Squarefree n) :
    (∑ d ∈ n.divisors, (1 : ℝ) / d) =
      ∏ p ∈ n.primeFactors, (1 + 1 / (p : ℝ)) := by
  simpa only [pow_zero] using sum_divisorReciprocalPower_eq_eulerProduct 0 hn

/-- An elementary exponential bound, before applying a sharp prime
reciprocal estimate. -/
theorem sum_divisorReciprocalPower_le_exp (k : ℕ) {n : ℕ} (hn : Squarefree n) :
    (∑ d ∈ n.divisors, (d.divisors.card : ℝ) ^ k / d) ≤
      Real.exp (2 ^ k * ∑ p ∈ n.primeFactors, (1 : ℝ) / p) := by
  rw [sum_divisorReciprocalPower_eq_eulerProduct k hn]
  calc
    (∏ p ∈ n.primeFactors, (1 + 2 ^ k / (p : ℝ))) ≤
        ∏ p ∈ n.primeFactors, Real.exp (2 ^ k / (p : ℝ)) := by
      apply Finset.prod_le_prod
      · intro p hp
        positivity
      · intro p hp
        simpa only [add_comm] using Real.add_one_le_exp (2 ^ k / (p : ℝ))
    _ = Real.exp (∑ p ∈ n.primeFactors, 2 ^ k / (p : ℝ)) := (Real.exp_sum _ _).symm
    _ = _ := by
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      ring

end Erdos587
