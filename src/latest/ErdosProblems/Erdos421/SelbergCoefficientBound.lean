import ErdosProblems.Erdos421.SelbergWeightBound
import ErdosProblems.Erdos421.UniformResidueSieve

/-! # Divisor bounds for the actual uniform upper-sieve weights -/

namespace Erdos421

theorem squarefree_divisors_card {n : ℕ} (hn : Squarefree n) :
    n.divisors.card = 2 ^ n.primeFactors.card := by
  rw [Nat.card_divisors hn.ne_zero]
  calc
    _ = ∏ _p ∈ n.primeFactors, 2 := by
      apply Finset.prod_congr rfl
      intro p hp
      rw [Nat.factorization_eq_one_of_squarefree hn
        (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp)]
    _ = _ := Finset.prod_const 2

theorem uniform_selberg_weight_abs_le (P : ℕ) (hP : Squarefree P) {D d : ℕ}
    (hD : 1 ≤ D) (hd : d ∣ P) :
    |selbergOptimizedWeight (uniformResidueSieve P hP) D d| ≤
      (2 : ℝ) ^ d.primeFactors.card := by
  let s := uniformResidueSieve P hP
  calc
    _ ≤ (s.nu d)⁻¹ * s.selbergTerms d := selbergOptimizedWeight_abs_le s hD hd
    _ = ∏ p ∈ d.primeFactors, (1 - (p : ℝ)⁻¹)⁻¹ := by
      rw [BoundingSieve.selbergTerms_apply, ← mul_assoc,
        inv_mul_cancel₀ (BoundingSieve.nu_ne_zero (s := s) hd), one_mul]
      rfl
    _ ≤ ∏ _p ∈ d.primeFactors, (2 : ℝ) := by
      apply Finset.prod_le_prod
      · intro p hp
        have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
        have hpinv : (p : ℝ)⁻¹ ≤ 1 / 2 := by
          rw [inv_eq_one_div, div_le_iff₀ (by linarith : 0 < (p : ℝ))]
          linarith
        exact inv_nonneg.mpr (by linarith)
      · intro p hp
        have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
        have hpinv : (p : ℝ)⁻¹ ≤ 1 / 2 := by
          rw [inv_eq_one_div, div_le_iff₀ (by linarith : 0 < (p : ℝ))]
          linarith
        rw [inv_eq_one_div, div_le_iff₀ (by linarith : 0 < 1 - (p : ℝ)⁻¹)]
        linarith
    _ = _ := Finset.prod_const 2

theorem uniform_selberg_lambda_abs_le (P : ℕ) (hP : Squarefree P) {D : ℕ}
    (hD : 1 ≤ D) (k : ℕ) :
    |BoundingSieve.lambdaSquared (selbergOptimizedWeight (uniformResidueSieve P hP) D) k| ≤
      (16 : ℝ) ^ k.primeFactors.card := by
  by_cases hk : k ∣ P
  · have hksq : Squarefree k := hP.squarefree_of_dvd hk
    have hw (d : ℕ) (hd : d ∈ k.divisors) :
        |selbergOptimizedWeight (uniformResidueSieve P hP) D d| ≤
          (2 : ℝ) ^ k.primeFactors.card := by
      apply (uniform_selberg_weight_abs_le P hP hD ((Nat.dvd_of_mem_divisors hd).trans hk)).trans
      apply pow_le_pow_right₀ (by norm_num)
      exact Finset.card_le_card (Nat.primeFactors_mono (Nat.dvd_of_mem_divisors hd) hksq.ne_zero)
    unfold BoundingSieve.lambdaSquared
    calc
      _ ≤ ∑ d ∈ k.divisors, ∑ e ∈ k.divisors,
          |if k = Nat.lcm d e then
            selbergOptimizedWeight (uniformResidueSieve P hP) D d *
            selbergOptimizedWeight (uniformResidueSieve P hP) D e else 0| := by
        apply (Finset.abs_sum_le_sum_abs _ _).trans
        exact Finset.sum_le_sum (fun _ _ ↦ Finset.abs_sum_le_sum_abs _ _)
      _ ≤ ∑ _d ∈ k.divisors, ∑ _e ∈ k.divisors,
          (2 : ℝ) ^ k.primeFactors.card * (2 : ℝ) ^ k.primeFactors.card := by
        apply Finset.sum_le_sum
        intro d hd
        apply Finset.sum_le_sum
        intro e he
        split_ifs
        · rw [abs_mul]
          exact mul_le_mul (hw d hd) (hw e he) (abs_nonneg _) (by positivity)
        · simp
      _ = (16 : ℝ) ^ k.primeFactors.card := by
        simp only [Finset.sum_const, nsmul_eq_mul, squarefree_divisors_card hksq,
          Nat.cast_pow, Nat.cast_ofNat]
        rw [← mul_assoc, ← mul_assoc, ← mul_pow, ← mul_pow, ← mul_pow]
        norm_num
  · rw [selbergLambdaSquared_eq_zero_of_not_dvd (uniformResidueSieve P hP) D hk, abs_zero]
    positivity

end Erdos421
