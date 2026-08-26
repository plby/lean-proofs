import ErdosProblems.Erdos421.SelbergCoefficientBound
import ErdosProblems.Erdos421.PrimeFactorCardGrowth

/-! # Uniform subpower growth for the constructed upper sieve -/

namespace Erdos421

theorem uniform_upper_sieve_coefficient_growth {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : ℕ) (hP : Squarefree P) (D : ℕ), 1 ≤ D →
      ∀ k : ℕ, 0 < k →
        |BoundingSieve.lambdaSquared
          (selbergOptimizedWeight (uniformResidueSieve P hP) D) k| ≤ C * (k : ℝ) ^ η := by
  obtain ⟨C, hC, hbound⟩ := primeFactorCard_power_bound (by norm_num : (1 : ℝ) ≤ 16) hη
  exact ⟨C, hC, fun P hP D hD k hk ↦
    (uniform_selberg_lambda_abs_le P hP hD k).trans (hbound k hk)⟩

theorem exists_bounded_finite_upper_sieve {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : ℕ) (_hP : Squarefree P) (z : ℝ), 2 ≤ z →
      (∀ p ∈ P.primeFactors, (p : ℝ) ≤ z) →
      ∀ (D : ℕ), 0 < D → ∀ (ε : ℝ), 0 < ε → ε ≤ 1 →
      16 * Real.exp 1 + Real.log (2 / ε) ≤ Real.log D / Real.log z →
      ∃ ρ : ℕ → ℝ, BoundingSieve.IsUpperMoebius ρ ∧
        (∀ k, D ^ 2 < k → ρ k = 0) ∧ (∀ k, ¬k ∣ P → ρ k = 0) ∧
        (∀ k, 0 < k → |ρ k| ≤ C * (k : ℝ) ^ η) ∧
        (∑ d ∈ P.divisors, ρ d / (d : ℝ)) ≤
          (1 + ε) * (∏ p ∈ P.primeFactors, (1 - (p : ℝ)⁻¹)) := by
  obtain ⟨C, hC, hbound⟩ := uniform_upper_sieve_coefficient_growth hη
  refine ⟨C, hC, ?_⟩
  intro P hP z hz hp D hD ε hε hε1 hlevel
  let s := uniformResidueSieve P hP
  let ρ := BoundingSieve.lambdaSquared (selbergOptimizedWeight s D)
  refine ⟨ρ, selbergOptimized_upperMoebius s hD,
    fun k hk ↦ selbergLambdaSquared_eq_zero_of_gt s hk,
    fun k hk ↦ selbergLambdaSquared_eq_zero_of_not_dvd s D hk,
    hbound P hP D hD, ?_⟩
  have hb := selbergOptimized_mainTerm_le_one_add s hz hp
    (fun p _ ↦ uniformResidueSieve_nu P hP p) hD hε hε1 hlevel
  change (∑ d ∈ P.divisors, ρ d * (d : ℝ)⁻¹) ≤
    (1 + ε) * (∏ p ∈ P.primeFactors, (1 - (p : ℝ)⁻¹)) at hb
  simpa only [div_eq_mul_inv] using hb

end Erdos421
