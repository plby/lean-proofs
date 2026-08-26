import ErdosProblems.Erdos421.ReciprocalPrimeVariation

/-! # Uniform reciprocal-prime summation on logarithmically comparable intervals -/

namespace Erdos421

theorem mertens_prime_interval {ε : ℝ} (hε : 0 < ε) :
    ∃ X₀ > 1, ∀ a b : ℝ, X₀ ≤ a → a ≤ b → 1 ≤ Real.log a →
      Real.log b ≤ 3 * Real.log a →
      |(∑ p ∈ primesInRealInterval a b, (p : ℝ)⁻¹) -
        Real.log (Real.log b / Real.log a)| ≤ ε := by
  obtain ⟨X₀, hX₀, hprime⟩ := prime_log_weighted_log_saving
    (by norm_num : (0 : ℝ) ≤ 0) (by positivity : 0 < ε / 6)
  refine ⟨X₀, hX₀, ?_⟩
  intro a b ha hab hlog hscale
  have ha1 := hX₀.trans_le ha
  have hsub : Set.Icc a b ⊆ Set.Ioi 1 := fun _ ht ↦ ha1.trans_le ht.1
  have hd : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ reciprocalPrimeWeight t :=
    fun t ht ↦ (reciprocalPrimeWeight_hasDerivAt (hsub ht)).differentiableAt
  have hc := reciprocalPrimeWeight_deriv_continuousOn.mono hsub
  have h := hprime a b ha hab reciprocalPrimeWeight hd hc
  simp only [Real.rpow_zero, div_one] at h
  have hsum : (∑ p ∈ primesInRealInterval a b, reciprocalPrimeWeight p * Real.log p) =
      ∑ p ∈ primesInRealInterval a b, (p : ℝ)⁻¹ := by
    apply Finset.sum_congr rfl
    intro p hp
    have hpp := (Finset.mem_filter.mp hp).2
    have hpr : (0 : ℝ) < p := by exact_mod_cast hpp.pos
    have hlp : 0 < Real.log p := Real.log_pos (by exact_mod_cast hpp.one_lt)
    dsimp only [reciprocalPrimeWeight]
    field_simp
  rw [hsum, reciprocalPrimeWeight_integral ha1 (ha1.trans_le hab)] at h
  calc
    _ ≤ _ := h
    _ ≤ (ε / 6) * 6 := mul_le_mul_of_nonneg_left
      (reciprocalPrimeWeight_variation_le ha1 hab hlog hscale) (by positivity)
    _ = _ := by ring

end Erdos421
