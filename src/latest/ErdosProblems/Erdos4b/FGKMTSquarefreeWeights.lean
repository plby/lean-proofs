/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTHarmonicConvolution

/-!
# Squarefree prime weights and their finite local convolutions

The common sieve coefficients use the multiplicative extension of `1 / g p`
with squarefree support and zero local weight at primes dividing the
pre-sieve modulus. The lemmas here retain this support literally and compute
all prime-power coefficients of a convolution of two such weights.
-/

namespace Erdos4b.FGKMT

noncomputable section

open ArithmeticFunction
open scoped BigOperators ArithmeticFunction.Moebius

/-- The squarefree multiplicative extension of prescribed prime weights. -/
def squarefreePrimeWeight (a : ℕ → ℝ) : ArithmeticFunction ℝ :=
  ((μ : ArithmeticFunction ℝ).pmul μ).pmul
    (ArithmeticFunction.prodPrimeFactors a)

theorem squarefreePrimeWeight_isMultiplicative (a : ℕ → ℝ) :
    (squarefreePrimeWeight a).IsMultiplicative := by
  exact (ArithmeticFunction.isMultiplicative_moebius.intCast.pmul
    ArithmeticFunction.isMultiplicative_moebius.intCast).pmul
      (ArithmeticFunction.IsMultiplicative.prodPrimeFactors a)

@[simp] theorem squarefreePrimeWeight_one (a : ℕ → ℝ) :
    squarefreePrimeWeight a 1 = 1 :=
  (squarefreePrimeWeight_isMultiplicative a).map_one

theorem squarefreePrimeWeight_apply_of_squarefree (a : ℕ → ℝ)
    {n : ℕ} (hn : Squarefree n) :
    squarefreePrimeWeight a n = ∏ p ∈ n.primeFactors, a p := by
  have hmu : (μ n : ℝ) ^ 2 = 1 := by
    exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree hn
  change (μ n : ℝ) * (μ n : ℝ) * ArithmeticFunction.prodPrimeFactors a n = _
  rw [← pow_two, hmu, one_mul, ArithmeticFunction.prodPrimeFactors_apply hn.ne_zero]

theorem squarefreePrimeWeight_apply_of_not_squarefree (a : ℕ → ℝ)
    {n : ℕ} (hn : ¬ Squarefree n) :
    squarefreePrimeWeight a n = 0 := by
  change (μ n : ℝ) * (μ n : ℝ) * ArithmeticFunction.prodPrimeFactors a n = 0
  rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hn]
  simp

theorem squarefreePrimeWeight_prime (a : ℕ → ℝ) {p : ℕ} (hp : p.Prime) :
    squarefreePrimeWeight a p = a p := by
  rw [squarefreePrimeWeight_apply_of_squarefree a hp.squarefree, hp.primeFactors]
  simp

theorem squarefreePrimeWeight_prime_pow_ge_two (a : ℕ → ℝ)
    {p j : ℕ} (hp : p.Prime) (hj : 2 ≤ j) :
    squarefreePrimeWeight a (p ^ j) = 0 := by
  have hmu : μ (p ^ j) = 0 := by
    rw [ArithmeticFunction.moebius_apply_prime_pow hp (by omega)]
    simp [show j ≠ 1 by omega]
  change (μ (p ^ j) : ℝ) * (μ (p ^ j) : ℝ) *
    ArithmeticFunction.prodPrimeFactors a (p ^ j) = 0
  rw [hmu]
  simp

/-- The divisor convolution at a prime power is the ordinary finite
coefficient convolution of its two local sequences. -/
theorem arithmetic_mul_prime_pow (f g : ArithmeticFunction ℝ)
    {p : ℕ} (hp : p.Prime) (j : ℕ) :
    (f * g) (p ^ j) = ∑ i ∈ Finset.range (j + 1), f (p ^ i) * g (p ^ (j - i)) := by
  rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal (fun x y => f x * g y),
    Nat.sum_divisors_prime_pow hp]
  apply Finset.sum_congr rfl
  intro i hi
  have hij : i ≤ j := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hi
  have hdiv : p ^ j / p ^ i = p ^ (j - i) := by
    conv_lhs => rw [show j = i + (j - i) by omega, pow_add]
    exact Nat.mul_div_cancel_left _ (pow_pos hp.pos i)
  rw [hdiv]

theorem squarefreePrimeWeight_mul_prime (a b : ℕ → ℝ)
    {p : ℕ} (hp : p.Prime) :
    (squarefreePrimeWeight a * squarefreePrimeWeight b) p = a p + b p := by
  conv_lhs => rw [show p = p ^ 1 by simp]
  rw [arithmetic_mul_prime_pow _ _ hp]
  norm_num [Finset.sum_range_succ, squarefreePrimeWeight_prime _ hp]
  ring

theorem squarefreePrimeWeight_mul_prime_sq (a b : ℕ → ℝ)
    {p : ℕ} (hp : p.Prime) :
    (squarefreePrimeWeight a * squarefreePrimeWeight b) (p ^ 2) = a p * b p := by
  rw [arithmetic_mul_prime_pow _ _ hp]
  norm_num [Finset.sum_range_succ, squarefreePrimeWeight_prime _ hp,
    squarefreePrimeWeight_prime_pow_ge_two _ hp (le_refl 2)]

theorem squarefreePrimeWeight_mul_prime_pow_ge_three (a b : ℕ → ℝ)
    {p j : ℕ} (hp : p.Prime) (hj : 3 ≤ j) :
    (squarefreePrimeWeight a * squarefreePrimeWeight b) (p ^ j) = 0 := by
  rw [arithmetic_mul_prime_pow _ _ hp]
  apply Finset.sum_eq_zero
  intro i hi
  by_cases hi2 : 2 ≤ i
  · rw [squarefreePrimeWeight_prime_pow_ge_two a hp hi2, zero_mul]
  · rw [squarefreePrimeWeight_prime_pow_ge_two b hp (by omega), mul_zero]

theorem divideByArgument_isMultiplicative {f : ArithmeticFunction ℝ}
    (hf : f.IsMultiplicative) : (divideByArgument f).IsMultiplicative := by
  refine ⟨by simp [hf.map_one], ?_⟩
  intro m n hmn
  simp only [divideByArgument_apply, hf.map_mul_of_coprime hmn, Nat.cast_mul,
    div_mul_div_comm]

theorem squarefreePrimeWeight_neg_reciprocal :
    squarefreePrimeWeight (fun p => -(1 / (p : ℝ))) = mobiusHarmonicArithmetic := by
  apply (ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers _
    (squarefreePrimeWeight_isMultiplicative _) _
      (divideByArgument_isMultiplicative ArithmeticFunction.isMultiplicative_moebius.intCast)).2
  intro p j hp
  rcases j with _ | j
  · simp
  · rcases j with _ | j
    · simp [squarefreePrimeWeight_prime _ hp, ArithmeticFunction.moebius_apply_prime hp,
        div_eq_mul_inv]
    · rw [squarefreePrimeWeight_prime_pow_ge_two _ hp (by omega),
        divideByArgument_apply, ArithmeticFunction.intCoe_apply,
        ArithmeticFunction.moebius_apply_prime_pow hp (by omega)]
      simp

theorem harmonicCorrection_squarefreePrimeWeight_prime (a : ℕ → ℝ)
    {p : ℕ} (hp : p.Prime) :
    harmonicCorrection (squarefreePrimeWeight a) p = a p - 1 / (p : ℝ) := by
  rw [harmonicCorrection, ← squarefreePrimeWeight_neg_reciprocal,
    squarefreePrimeWeight_mul_prime a _ hp]
  ring

theorem harmonicCorrection_squarefreePrimeWeight_prime_sq (a : ℕ → ℝ)
    {p : ℕ} (hp : p.Prime) :
    harmonicCorrection (squarefreePrimeWeight a) (p ^ 2) = -a p / (p : ℝ) := by
  rw [harmonicCorrection, ← squarefreePrimeWeight_neg_reciprocal,
    squarefreePrimeWeight_mul_prime_sq a _ hp]
  ring

theorem harmonicCorrection_squarefreePrimeWeight_prime_pow_ge_three (a : ℕ → ℝ)
    {p j : ℕ} (hp : p.Prime) (hj : 3 ≤ j) :
    harmonicCorrection (squarefreePrimeWeight a) (p ^ j) = 0 := by
  rw [harmonicCorrection, ← squarefreePrimeWeight_neg_reciprocal]
  exact squarefreePrimeWeight_mul_prime_pow_ge_three a _ hp hj

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.harmonicCorrection_squarefreePrimeWeight_prime_pow_ge_three
