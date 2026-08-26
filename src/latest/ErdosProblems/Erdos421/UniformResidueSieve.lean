import ErdosProblems.Erdos421.SelbergUpperApproximation
import ErdosProblems.Erdos421.SelbergSupport

/-! # Sieve weights for the uniform divisibility densities `1 / d` -/

namespace Erdos421

noncomputable def reciprocalDivisibilityDensity : ArithmeticFunction ℝ :=
  ⟨fun n ↦ (n : ℝ)⁻¹, by simp⟩

theorem reciprocalDivisibilityDensity_apply (n : ℕ) :
    reciprocalDivisibilityDensity n = (n : ℝ)⁻¹ := rfl

theorem reciprocalDivisibilityDensity_isMultiplicative :
    reciprocalDivisibilityDensity.IsMultiplicative := by
  constructor
  · simp [reciprocalDivisibilityDensity_apply]
  · intro m n hcop
    simp only [reciprocalDivisibilityDensity_apply, Nat.cast_mul, mul_inv]

/-- The reference sieve on one complete system of residues. Its multiplicative
density is the actual divisibility density `1 / d`. -/
noncomputable def uniformResidueSieve (P : ℕ) (hP : Squarefree P) : BoundingSieve where
  support := Finset.range P
  prodPrimes := P
  prodPrimes_squarefree := hP
  weights := fun _ ↦ 1
  weights_nonneg := fun _ ↦ zero_le_one
  totalMass := P
  nu := reciprocalDivisibilityDensity
  nu_mult := reciprocalDivisibilityDensity_isMultiplicative
  nu_pos_of_prime := by
    intro p hp hpd
    rw [reciprocalDivisibilityDensity_apply]
    exact inv_pos.mpr (by exact_mod_cast hp.pos)
  nu_lt_one_of_prime := by
    intro p hp hpd
    rw [reciprocalDivisibilityDensity_apply]
    exact (inv_lt_one₀ (by exact_mod_cast hp.pos)).mpr (by exact_mod_cast hp.one_lt)

theorem uniformResidueSieve_nu (P : ℕ) (hP : Squarefree P) (d : ℕ) :
    (uniformResidueSieve P hP).nu d = (d : ℝ)⁻¹ := rfl

theorem uniformResidueSieve_euler (P : ℕ) (hP : Squarefree P) :
    sieveEulerProduct (uniformResidueSieve P hP) = ∏ p ∈ P.primeFactors, (1 - (p : ℝ)⁻¹) := rfl

theorem exists_finite_upper_sieve (P : ℕ) (hP : Squarefree P) {z : ℝ} (hz : 2 ≤ z)
    (hprimes : ∀ p ∈ P.primeFactors, (p : ℝ) ≤ z)
    {D : ℕ} (hD : 0 < D) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hlevel : 16 * Real.exp 1 + Real.log (2 / ε) ≤ Real.log D / Real.log z) :
    ∃ ρ : ℕ → ℝ, BoundingSieve.IsUpperMoebius ρ ∧
      (∀ k, D ^ 2 < k → ρ k = 0) ∧ (∀ k, ¬k ∣ P → ρ k = 0) ∧
      (∑ d ∈ P.divisors, ρ d / (d : ℝ)) ≤
        (1 + ε) * (∏ p ∈ P.primeFactors, (1 - (p : ℝ)⁻¹)) := by
  let s := uniformResidueSieve P hP
  let ρ := BoundingSieve.lambdaSquared (selbergOptimizedWeight s D)
  refine ⟨ρ, selbergOptimized_upperMoebius s hD,
    fun k hk ↦ selbergLambdaSquared_eq_zero_of_gt s hk,
    fun k hk ↦ selbergLambdaSquared_eq_zero_of_not_dvd s D hk, ?_⟩
  have hb := selbergOptimized_mainTerm_le_one_add s hz hprimes
    (fun p _ ↦ uniformResidueSieve_nu P hP p) hD hε hε1 hlevel
  change (∑ d ∈ P.divisors, ρ d * (d : ℝ)⁻¹) ≤
    (1 + ε) * (∏ p ∈ P.primeFactors, (1 - (p : ℝ)⁻¹)) at hb
  simpa only [div_eq_mul_inv] using hb

end Erdos421
