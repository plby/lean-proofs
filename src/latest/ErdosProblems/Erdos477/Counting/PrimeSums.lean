/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
An explicit lower bound for the logarithmically weighted prime reciprocal sum.
Formal author: Codex.
-/

import ErdosProblems.Erdos477.Counting.PrimeWeights

namespace Erdos477.Counting

open scoped BigOperators

lemma primeFactors_factorial (N : ℕ) :
    (Nat.factorial N).primeFactors = Nat.primesLE N := by
  ext p
  rw [Nat.mem_primeFactors, Nat.mem_primesLE]
  constructor
  · rintro ⟨hp, hd, _⟩
    exact ⟨hp.dvd_factorial.mp hd, hp⟩
  · rintro ⟨hN, hp⟩
    exact ⟨hp, hp.dvd_factorial.mpr hN, Nat.factorial_ne_zero N⟩

lemma log_factorial_eq_sum (N : ℕ) :
    Real.log (Nat.factorial N) =
      ∑ p ∈ Nat.primesLE N, ((Nat.factorial N).factorization p : ℝ) * Real.log p := by
  have hfac := Nat.prod_primeFactors_pow_factorization (Nat.factorial_ne_zero N)
  have hcast : (Nat.factorial N : ℝ) =
      ∏ p ∈ (Nat.factorial N).primeFactors, (p : ℝ) ^ (Nat.factorial N).factorization p := by
    exact_mod_cast hfac
  calc
    _ = Real.log (∏ p ∈ (Nat.factorial N).primeFactors,
        (p : ℝ) ^ (Nat.factorial N).factorization p) := congrArg Real.log hcast
    _ = ∑ p ∈ (Nat.factorial N).primeFactors,
        ((Nat.factorial N).factorization p : ℝ) * Real.log p := by
      rw [Real.log_prod]
      · simp only [Real.log_pow]
      · intro p hp
        exact pow_ne_zero _ (by
          exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero)
    _ = _ := by rw [primeFactors_factorial]

lemma factorization_factorial_le_real_div (N p : ℕ) (hp : p.Prime) :
    ((Nat.factorial N).factorization p : ℝ) ≤ (N : ℝ) / ((p : ℝ) - 1) := by
  have hnat : (p - 1) * (Nat.factorial N).factorization p ≤ N := by
    rw [Nat.sub_one_mul_factorization_factorial hp]
    exact Nat.sub_le _ _
  have hreal : ((p - 1 : ℕ) : ℝ) * ((Nat.factorial N).factorization p : ℝ) ≤ N := by
    exact_mod_cast hnat
  rw [Nat.cast_sub hp.one_le, Nat.cast_one] at hreal
  have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by
    have h : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    linarith
  exact (le_div_iff₀ hp1).mpr (by nlinarith)

lemma log_factorial_le_prime_sum (N : ℕ) :
    Real.log (Nat.factorial N) ≤
      (N : ℝ) * ∑ p ∈ Nat.primesLE N, Real.log p / ((p : ℝ) - 1) := by
  rw [log_factorial_eq_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hp
  have hp' := (Nat.mem_primesLE.mp hp).2
  have hlog : 0 ≤ Real.log (p : ℝ) := Real.log_natCast_nonneg p
  have h := mul_le_mul_of_nonneg_right (factorization_factorial_le_real_div N p hp') hlog
  convert h using 1; ring

lemma log_factorial_lower (N : ℕ) (hN : 1 ≤ N) :
    (N : ℝ) * Real.log N - N ≤ Real.log (Nat.factorial N) := by
  have h := Stirling.le_log_factorial_stirling (n := N) (by omega)
  have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_natCast_nonneg N
  have hpi : 0 ≤ Real.log (2 * Real.pi) := Real.log_nonneg (by
    have := Real.pi_gt_three
    linarith)
  linarith

/-- The lower half of the first Mertens estimate, with an explicit constant. -/
theorem log_sub_three_le_prime_sum (N : ℕ) (hN : 1 ≤ N) :
    Real.log (N : ℝ) - 3 ≤ ∑ p ∈ Nat.primesLE N, Real.log p / (p : ℝ) := by
  have hfac := log_factorial_lower N hN
  have hupp := log_factorial_le_prime_sum N
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hpred : Real.log (N : ℝ) - 1 ≤
      ∑ p ∈ Nat.primesLE N, Real.log p / ((p : ℝ) - 1) := by
    nlinarith
  have hsplit :
      (∑ p ∈ Nat.primesLE N, Real.log p / ((p : ℝ) - 1)) =
      (∑ p ∈ Nat.primesLE N, Real.log p / (p : ℝ)) +
        ∑ p ∈ Nat.primesLE N, Real.log p / ((p : ℝ) * (p - 1)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p hp
    have hp' := (Nat.mem_primesLE.mp hp).2
    have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp'.ne_zero
    have hp1 : (p : ℝ) - 1 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hp'.ne_one)
    field_simp
    ring
  rw [hsplit] at hpred
  have herr := sum_prime_error_le N
  linarith

#print axioms log_sub_three_le_prime_sum
-- 'Erdos477.Counting.log_sub_three_le_prime_sum' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

end Erdos477.Counting
