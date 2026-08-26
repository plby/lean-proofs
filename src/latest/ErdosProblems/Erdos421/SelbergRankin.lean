import ErdosProblems.Erdos421.SelbergWeights
import ErdosProblems.Erdos421.ArithmeticRpow

/-! # A Rankin bound for the omitted Selberg normalizer terms -/

namespace Erdos421

theorem selbergNormalizer_rankin (s : BoundingSieve) {D : ℕ} (hD : 0 < D)
    {α : ℝ} (hα : 0 ≤ α) :
    (∏ p ∈ s.prodPrimes.primeFactors, (1 + s.selbergTerms p)) -
      ((D : ℝ) ^ α)⁻¹ * (∏ p ∈ s.prodPrimes.primeFactors,
        (1 + s.selbergTerms p * (p : ℝ) ^ α)) ≤ selbergNormalizer s D := by
  have hDp : (0 : ℝ) < D := by exact_mod_cast hD
  have hDpow : 0 < (D : ℝ) ^ α := Real.rpow_pos_of_pos hDp _
  have hp (d : ℕ) (hd : d ∈ s.prodPrimes.divisors) : s.selbergTerms d ≤
      (if d ≤ D then s.selbergTerms d else 0) +
        ((D : ℝ) ^ α)⁻¹ * (s.selbergTerms d * (d : ℝ) ^ α) := by
    have hg := (BoundingSieve.selbergTerms_pos (s := s) (Nat.dvd_of_mem_divisors hd)).le
    by_cases hsmall : d ≤ D
    · rw [if_pos hsmall]
      exact le_add_of_nonneg_right (by positivity)
    · rw [if_neg hsmall, zero_add]
      have hDd : (D : ℝ) ≤ d := by exact_mod_cast (by omega : D ≤ d)
      have hpow := Real.rpow_le_rpow hDp.le hDd hα
      have hb : s.selbergTerms d ≤ (s.selbergTerms d * (d : ℝ) ^ α) / (D : ℝ) ^ α :=
        (le_div_iff₀ hDpow).mpr (mul_le_mul_of_nonneg_left hpow hg)
      simpa only [div_eq_mul_inv, mul_comm] using hb
  have hb := Finset.sum_le_sum hp
  rw [Finset.sum_add_distrib, ← Finset.sum_filter, ← Finset.mul_sum] at hb
  change (∑ d ∈ s.prodPrimes.divisors, s.selbergTerms d) ≤ selbergNormalizer s D +
    ((D : ℝ) ^ α)⁻¹ * (∑ d ∈ s.prodPrimes.divisors, s.selbergTerms d * (d : ℝ) ^ α) at hb
  rw [← BoundingSieve.selbergTerms_isMultiplicative.prodPrimeFactors_one_add_of_squarefree
    s.prodPrimes_squarefree,
    sum_divisors_multiplicative_rpow s.selbergTerms
      BoundingSieve.selbergTerms_isMultiplicative s.prodPrimes_squarefree α] at hb
  linarith

end Erdos421
