import Mathlib.NumberTheory.ArithmeticFunction.Liouville
import Mathlib.Tactic

/-! # The indicator of positive squares as a Dirichlet convolution -/

namespace Erdos941.Analytic

open ArithmeticFunction Finset

noncomputable def squareIndicator : ArithmeticFunction ℤ :=
  (zeta : ArithmeticFunction ℤ) * liouville

theorem squareIndicator_multiplicative : squareIndicator.IsMultiplicative :=
  isMultiplicative_zeta.natCast.mul isMultiplicative_liouville

theorem squareIndicator_prime_pow {p : ℕ} (hp : p.Prime) (k : ℕ) :
    squareIndicator (p ^ k) = if Even k then 1 else 0 := by
  simp only [squareIndicator, coe_zeta_mul_apply, Nat.sum_divisors_prime_pow hp,
    liouville_apply (pow_ne_zero _ hp.ne_zero), cardFactors_apply_prime_pow hp,
    neg_one_geom_sum, Nat.even_add_one]
  by_cases hk : Even k <;> simp [hk]

theorem squareIndicator_nonzero_isSquare {n : ℕ} (h : squareIndicator n ≠ 0) :
    IsSquare n := by
  classical
  have hn : n ≠ 0 := by intro hn; simpa [hn] using h
  rw [squareIndicator_multiplicative.multiplicative_factorization _ hn] at h
  change (∏ p ∈ n.primeFactors, squareIndicator (p ^ n.factorization p)) ≠ 0 at h
  have heven (p : ℕ) (hp : p ∈ n.primeFactors) : Even (n.factorization p) := by
    have hh := Finset.prod_ne_zero_iff.mp h p hp
    rw [squareIndicator_prime_pow (Nat.prime_of_mem_primeFactors hp)] at hh
    by_contra he
    simp [he] at hh
  let c := ∏ p ∈ n.primeFactors, p ^ (n.factorization p / 2)
  apply (isSquare_iff_exists_sq n).mpr
  refine ⟨c, ?_⟩
  rw [Nat.prod_primeFactors_pow_factorization hn]
  dsimp [c]
  rw [← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro p hp
  rw [← pow_mul]
  congr 1
  have hd : 2 ∣ n.factorization p := even_iff_two_dvd.mp (heven p hp)
  exact (Nat.div_mul_cancel hd).symm

theorem squareIndicator_square {c : ℕ} (hc : c ≠ 0) : squareIndicator (c ^ 2) = 1 := by
  classical
  rw [squareIndicator_multiplicative.multiplicative_factorization _ (pow_ne_zero 2 hc)]
  apply Finset.prod_eq_one
  intro p hp
  have hp' : p.Prime := Nat.prime_of_mem_primeFactors hp
  change squareIndicator (p ^ (c ^ 2).factorization p) = 1
  rw [squareIndicator_prime_pow hp', if_pos]
  simp only [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
  exact even_two_mul _

theorem squareIndicator_eq (n : ℕ) :
    squareIndicator n = if n ≠ 0 ∧ IsSquare n then 1 else 0 := by
  classical
  split_ifs with h
  · obtain ⟨c, hc⟩ := h.2.exists_sq
    rw [hc]
    exact squareIndicator_square (by intro hz; simp [hz] at hc; exact h.1 hc)
  · by_contra hn
    apply h
    exact ⟨by intro hz; simpa [hz] using hn, squareIndicator_nonzero_isSquare hn⟩

theorem squareIndicator_nonneg (n : ℕ) : 0 ≤ squareIndicator n := by
  rw [squareIndicator_eq]
  split_ifs <;> norm_num

theorem squareIndicator_le_one (n : ℕ) : squareIndicator n ≤ 1 := by
  rw [squareIndicator_eq]
  split_ifs <;> norm_num

end Erdos941.Analytic
