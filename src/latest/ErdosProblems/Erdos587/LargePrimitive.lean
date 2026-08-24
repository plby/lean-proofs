import ErdosProblems.Erdos587.CriticalTerminal

/-! Combined wider and critical branches for a non-small primitive coefficient. -/

namespace Erdos587

theorem exists_large_primitive_terminal (C : ℝ) (hC : 0 < C) :
    ∃ B : ℕ, 0 < B ∧ ∃ T₀ : ℝ, ∀ (t u v H J T : ℕ), T₀ ≤ (T : ℝ) →
      0 < u → 0 < v → 0 < H → 0 < J → u.Coprime v →
      t + u * H + v * J ≤ T → u * H ≤ v * J →
      (T : ℝ) ≤ C * ((u * H + v * J : ℕ) : ℝ) →
      (∀ x₁ ≤ H, ∀ y₁ ≤ J, ∀ x₂ ≤ H, ∀ y₂ ≤ J,
        t + u * x₁ + v * y₁ = t + u * x₂ + v * y₂ → x₁ = x₂ ∧ y₁ = y₂) →
      (T : ℝ) ^ (1 / 16 : ℝ) ≤ u →
      (T : ℝ) ^ (1 / 4 : ℝ) * (1 + Real.log T) ^ B ≤ H →
      (T : ℝ) ^ (1 / 4 : ℝ) * (1 + Real.log T) ^ B ≤ J →
      (T : ℝ) ^ (3 / 4 : ℝ) * (1 + Real.log T) ^ B ≤ (H : ℝ) * J →
      ∃ x ≤ H, ∃ y ≤ J, ∃ z : ℕ, 0 < z ∧ z ^ 2 = t + u * x + v * y := by
  obtain ⟨B₁, hB₁, T₁, hwide⟩ := exists_wide_primitive_terminal C hC
  obtain ⟨B₂, hB₂, T₂, hcritical⟩ := exists_critical_primitive_terminal C hC
  refine ⟨max B₁ B₂, lt_of_lt_of_le hB₁ (le_max_left _ _), max 1 (max T₁ T₂), ?_⟩
  intro t u v H J T hbig hu hv hH hJ huv hambient horient hspan hproper hu0 hsideH hsideJ hprod
  have hT1 : (1 : ℝ) ≤ T := (le_max_left _ _).trans hbig
  have hTw : T₁ ≤ (T : ℝ) := (le_max_left T₁ T₂).trans ((le_max_right _ _).trans hbig)
  have hTc : T₂ ≤ (T : ℝ) := (le_max_right T₁ T₂).trans ((le_max_right _ _).trans hbig)
  have hΛ1 : (1 : ℝ) ≤ 1 + Real.log T := by have := Real.log_nonneg hT1; linarith
  have hpoww := pow_le_pow_right₀ hΛ1 (le_max_left B₁ B₂)
  have hpowc := pow_le_pow_right₀ hΛ1 (le_max_right B₁ B₂)
  by_cases hJwide : (T : ℝ) ^ (1 / 4 + 1 / 1000 : ℝ) ≤ J
  · apply hwide t u v H J T hTw hv hJ huv hambient horient hspan _ _ hJwide
    · exact (mul_le_mul_of_nonneg_left hpoww (Real.rpow_nonneg (by positivity) _)).trans hsideH
    · exact (mul_le_mul_of_nonneg_left hpoww (Real.rpow_nonneg (by positivity) _)).trans hprod
  · have hHv := (first_side_lt_step_of_proper hv horient hproper).le
    apply hcritical t u v H J T hTc hu hv hH hHv huv hambient horient hspan hu0
      (le_of_lt (lt_of_not_ge hJwide))
    · exact (mul_le_mul_of_nonneg_left hpowc (Real.rpow_nonneg (by positivity) _)).trans hsideJ
    · exact (mul_le_mul_of_nonneg_left hpowc (Real.rpow_nonneg (by positivity) _)).trans hprod

end Erdos587
