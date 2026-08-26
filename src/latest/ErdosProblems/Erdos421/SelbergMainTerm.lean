import ErdosProblems.Erdos421.SelbergWeights

/-! # The exact main term of the constructed Selberg upper sieve -/

namespace Erdos421

open scoped ArithmeticFunction.Moebius

theorem selbergOptimized_mainTerm (s : BoundingSieve) {D : ℕ} (hD : 1 ≤ D) :
    s.mainSum (BoundingSieve.lambdaSquared (selbergOptimizedWeight s D)) =
      1 / selbergNormalizer s D := by
  have hG := selbergNormalizer_pos s hD
  rw [BoundingSieve.mainSum_lambdaSquared_eq_sum_mul_sum_sq]
  have hrow : (∑ l ∈ s.prodPrimes.divisors, (s.selbergTerms l)⁻¹ *
      (∑ d ∈ s.prodPrimes.divisors,
        if l ∣ d then s.nu d * selbergOptimizedWeight s D d else 0) ^ 2) =
      ∑ l ∈ s.prodPrimes.divisors, (s.selbergTerms l)⁻¹ * (selbergTarget s D l) ^ 2 := by
    apply Finset.sum_congr rfl
    intro l hl
    rw [selbergOptimizedWeight_row s D (Nat.dvd_of_mem_divisors hl)]
  rw [hrow]
  calc
    _ = ∑ l ∈ s.prodPrimes.divisors.filter (fun l ↦ l ≤ D),
        s.selbergTerms l / (selbergNormalizer s D) ^ 2 := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro l hl
      have hg := BoundingSieve.selbergTerms_pos (s := s) (Nat.dvd_of_mem_divisors hl)
      have hμ : (μ l : ℝ) ^ 2 = 1 := by
        exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree
          (BoundingSieve.squarefree_of_mem_divisors_prodPrimes (s := s) hl)
      rw [selbergTarget]
      split_ifs
      · rw [div_pow, mul_pow, hμ, one_mul]
        field_simp
      · simp
    _ = selbergNormalizer s D / (selbergNormalizer s D) ^ 2 := by
      rw [← Finset.sum_div]
      rfl
    _ = _ := by field_simp

theorem selbergOptimized_upperMoebius (s : BoundingSieve) {D : ℕ} (hD : 1 ≤ D) :
    BoundingSieve.IsUpperMoebius (BoundingSieve.lambdaSquared (selbergOptimizedWeight s D)) :=
  BoundingSieve.upperMoebius_lambdaSquared _ (selbergOptimizedWeight_one s hD)

end Erdos421
