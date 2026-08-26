import ErdosProblems.Erdos67b.MRSmoothPrimeWeightMass

/-! # Sparse prime energy for the actual coefficients f(p)/p -/

open scoped BigOperators

namespace Erdos67b

noncomputable section

def mrSparsePrimeNormalizedBudget (R : ℕ) (P : ℝ) (N : ℕ) : ℝ :=
  20000 * mrPrimeBlockMassConstant / (mrPrimeSieveExponent R * (Real.log P) ^ 2) +
    mrPrimeKernelErrorConstant R * mrPrimeBlockMassConstant * N /
      (P ^ mrPrimeKernelSaving R * Real.log P)

theorem mrSparsePrimeNormalizedBudget_nonneg (R : ℕ) {P : ℝ} (hP : 1 ≤ P) (N : ℕ) :
    0 ≤ mrSparsePrimeNormalizedBudget R P N := by
  have := mrPrimeSieveExponent_pos R
  have := mrPrimeKernelErrorConstant_pos R
  have := mrPrimeBlockMassConstant_pos
  have := Real.log_nonneg hP
  unfold mrSparsePrimeNormalizedBudget
  positivity

theorem mrSum_norm_primeLineCoefficients_le (A : Finset ℕ)
    (f : ℕ → ℂ) (hf : ∀ p ∈ A, ‖f p‖ ≤ 1) :
    (∑ p ∈ A, ‖f p / (p : ℂ)‖ ^ 2) ≤ ∑ p ∈ A, 1 / (p : ℝ) ^ 2 := by
  apply Finset.sum_le_sum
  intro p hp
  rw [norm_div, Complex.norm_natCast, div_pow]
  apply div_le_div_of_nonneg_right _ (sq_nonneg (p : ℝ))
  have hh := pow_le_pow_left₀ (norm_nonneg (f p)) (hf p hp) 2
  simpa only [one_pow] using hh

theorem mrExists_sparsePrime_normalized_energy_bound (R : ℕ) (hR : 2 ≤ R)
    {h : ℝ} (hhR : 2 * h ≤ (R : ℝ)) :
    ∃ P₀ : ℝ, 1 < P₀ ∧ ∀ P ≥ P₀,
      ∀ A : Finset ℕ, (∀ p ∈ A, p.Prime) →
        (∀ p ∈ A, (p : ℝ) ∈ Set.Icc P (2 * P)) →
      ∀ S : Finset ℝ,
        (∀ s ∈ S, ∀ t ∈ S, s ≠ t → 1 ≤ |s - t|) →
        (∀ s ∈ S, ∀ t ∈ S, |t - s| ≤ P ^ h) →
      ∀ f : ℕ → ℂ, (∀ p ∈ A, ‖f p‖ ≤ 1) →
        (∑ t ∈ S, ‖logarithmicDirichletPolynomial A (fun p ↦ f p / (p : ℂ)) t‖ ^ 2) ≤
          mrSparsePrimeNormalizedBudget R P S.card := by
  obtain ⟨P₁, hP₁one, hP₁⟩ := mrExists_sparsePrime_energy_bound R hR hhR
  obtain ⟨P₂, _, hP₂⟩ := mrExists_primeBlock_inverse_square_mass
  refine ⟨max P₁ P₂, hP₁one.trans_le (le_max_left _ _), ?_⟩
  intro P hP A hprime hblock S hsep hdiam f hf
  have hPfirst : P₁ ≤ P := (le_max_left P₁ P₂).trans hP
  have hPsecond : P₂ ≤ P := (le_max_right P₁ P₂).trans hP
  have hPone : 1 < P := hP₁one.trans_le hPfirst
  have hPpos : 0 < P := by linarith
  have hlog : 0 < Real.log P := Real.log_pos hPone
  have hk := mrPrimeSieveExponent_pos R
  have hmass := (mrSum_norm_primeLineCoefficients_le A f hf).trans
    (hP₂ P hPsecond A hprime hblock)
  have hb := hP₁ P hPfirst A hprime hblock S hsep hdiam (fun p ↦ f p / (p : ℂ))
  apply hb.trans
  calc
    _ ≤ mrSparsePrimeGramBudget R P S.card * (mrPrimeBlockMassConstant / (P * Real.log P)) :=
      mul_le_mul_of_nonneg_left hmass (mrSparsePrimeGramBudget_nonneg R hPone.le S.card)
    _ = mrSparsePrimeNormalizedBudget R P S.card := by
      unfold mrSparsePrimeGramBudget mrSparsePrimeNormalizedBudget
      rw [Real.rpow_sub hPpos, Real.rpow_one]
      field_simp

end

end Erdos67b
