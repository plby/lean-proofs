import ErdosProblems.Erdos587.HooleyConvolution
import ErdosProblems.Erdos421.ArithmeticRpow

/-!
# Nonnegative divisor weights for Rankin's trick

The real-power function is the divisor sum of its Möbius transform. For
nonnegative exponents the transform is nonnegative, so it can be inserted
into the harmonic Delta convolution inequality.
-/

open scoped BigOperators ArithmeticFunction.Moebius ArithmeticFunction.zeta

namespace Erdos587

noncomputable def deltaRankinWeight (β : ℝ) : ArithmeticFunction ℝ :=
  Erdos421.arithmeticRpow β * (ArithmeticFunction.moebius : ArithmeticFunction ℝ)

lemma deltaRankinWeight_isMultiplicative (β : ℝ) : (deltaRankinWeight β).IsMultiplicative :=
  (Erdos421.arithmeticRpow_isMultiplicative β).mul
    ArithmeticFunction.isMultiplicative_moebius.intCast

lemma sum_divisors_deltaRankinWeight {n : ℕ} (hn : n ≠ 0) (β : ℝ) :
    (∑ d ∈ n.divisors, deltaRankinWeight β d) = (n : ℝ) ^ β := by
  rw [← ArithmeticFunction.coe_mul_zeta_apply]
  have heq : deltaRankinWeight β * (ArithmeticFunction.zeta : ArithmeticFunction ℝ) =
      Erdos421.arithmeticRpow β := by
    rw [deltaRankinWeight, mul_assoc, ArithmeticFunction.coe_moebius_mul_coe_zeta, mul_one]
  rw [heq, Erdos421.arithmeticRpow_apply hn]

lemma deltaRankinWeight_prime_pow {p : ℕ} (hp : p.Prime) (k : ℕ) (β : ℝ) :
    deltaRankinWeight β (p ^ (k + 1)) =
      ((p : ℝ) ^ (k + 1)) ^ β - ((p : ℝ) ^ k) ^ β := by
  have hnext := sum_divisors_deltaRankinWeight (pow_ne_zero (k + 1) hp.ne_zero) β
  have hprev := sum_divisors_deltaRankinWeight (pow_ne_zero k hp.ne_zero) β
  rw [Nat.sum_divisors_prime_pow hp, Finset.sum_range_succ] at hnext
  rw [Nat.sum_divisors_prime_pow hp] at hprev
  simp only [Nat.cast_pow] at hnext hprev
  linarith

lemma deltaRankinWeight_nonneg {β : ℝ} (hβ : 0 ≤ β) (n : ℕ) :
    0 ≤ deltaRankinWeight β n := by
  by_cases hn : n = 0
  · subst n
    simp
  · rw [(deltaRankinWeight_isMultiplicative β).multiplicative_factorization _ hn]
    apply Finset.prod_nonneg
    intro p hp
    have hpprime := Nat.prime_of_mem_primeFactors hp
    have hepos : n.factorization p ≠ 0 := Finsupp.mem_support_iff.mp hp
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hepos
    rw [hk]
    change 0 ≤ deltaRankinWeight β (p ^ (k + 1))
    rw [deltaRankinWeight_prime_pow hpprime]
    apply sub_nonneg.mpr
    exact Real.rpow_le_rpow (by positivity)
      (pow_le_pow_right₀ (by exact_mod_cast hpprime.one_le) (Nat.le_succ k)) hβ

theorem delta_rankin_harmonic_bound (N : ℕ) {β : ℝ} (hβ : 0 ≤ β) :
    (∑ n ∈ Finset.Icc 1 N, ((hooleyDelta n : ℝ) / n) * (n : ℝ) ^ β) ≤
      (∑ d ∈ Finset.Icc 1 N, (d.divisors.card : ℝ) * deltaRankinWeight β d / d) *
        ∑ m ∈ Finset.Icc 1 N, (hooleyDelta m : ℝ) / m := by
  have h := delta_harmonic_divisor_twist_le N (deltaRankinWeight β) (deltaRankinWeight_nonneg hβ)
  have heq : (∑ n ∈ Finset.Icc 1 N, ((hooleyDelta n : ℝ) / n) *
      ∑ d ∈ n.divisors, deltaRankinWeight β d) =
        ∑ n ∈ Finset.Icc 1 N, ((hooleyDelta n : ℝ) / n) * (n : ℝ) ^ β := by
    apply Finset.sum_congr rfl
    intro n hn
    rw [sum_divisors_deltaRankinWeight (by have := (Finset.mem_Icc.mp hn).1; omega)]
  rw [heq] at h
  exact h

end Erdos587
