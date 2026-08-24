import ErdosProblems.Erdos587.LargePrimitive
import ErdosProblems.Erdos587.SmallPrimitive

/-! The primitive terminal rectangle, including small coefficients. -/

namespace Erdos587

theorem exists_primitive_terminal (C : ℝ) (hC : 0 < C) :
    ∃ B : ℕ, 0 < B ∧ ∃ T₀ : ℝ, ∀ (t u v H J T : ℕ), T₀ ≤ (T : ℝ) →
      0 < u → 0 < v → 0 < H → 0 < J → u.Coprime v →
      t + u * H + v * J ≤ T → u * H ≤ v * J →
      (T : ℝ) ≤ C * ((u * H + v * J : ℕ) : ℝ) →
      (∀ x₁ ≤ H, ∀ y₁ ≤ J, ∀ x₂ ≤ H, ∀ y₂ ≤ J,
        t + u * x₁ + v * y₁ = t + u * x₂ + v * y₂ → x₁ = x₂ ∧ y₁ = y₂) →
      (T : ℝ) ^ (1 / 4 : ℝ) * (1 + Real.log T) ^ B ≤ H →
      (T : ℝ) ^ (1 / 4 : ℝ) * (1 + Real.log T) ^ B ≤ J →
      (T : ℝ) ^ (3 / 4 : ℝ) * (1 + Real.log T) ^ B ≤ (H : ℝ) * J →
      ∃ x ≤ H, ∃ y ≤ J, ∃ z : ℕ, 0 < z ∧ z ^ 2 = t + u * x + v * y := by
  obtain ⟨B₁, hB₁, T₁, hwide⟩ := exists_wide_primitive_terminal C hC
  obtain ⟨B₂, hB₂, T₂, hcritical⟩ := exists_critical_primitive_terminal C hC
  obtain ⟨T₃, hsmall⟩ := exists_small_primitive_terminal C hC
  refine ⟨max B₁ B₂, lt_of_lt_of_le hB₁ (le_max_left _ _),
    max 1 (max T₁ (max T₂ T₃)), ?_⟩
  intro t u v H J T hbig hu hv hH hJ huv hambient horient hspan hproper hsideH hsideJ hprod
  have hT1 : (1 : ℝ) ≤ T := (le_max_left _ _).trans hbig
  have hthreshold : max T₁ (max T₂ T₃) ≤ (T : ℝ) := (le_max_right _ _).trans hbig
  have hTw : T₁ ≤ (T : ℝ) := (le_max_left _ _).trans hthreshold
  have hTc : T₂ ≤ (T : ℝ) := (le_max_left T₂ T₃).trans ((le_max_right _ _).trans hthreshold)
  have hTs : T₃ ≤ (T : ℝ) := (le_max_right T₂ T₃).trans ((le_max_right _ _).trans hthreshold)
  have hΛ1 : (1 : ℝ) ≤ 1 + Real.log T := by have := Real.log_nonneg hT1; linarith
  have hpoww := pow_le_pow_right₀ hΛ1 (le_max_left B₁ B₂)
  have hpowc := pow_le_pow_right₀ hΛ1 (le_max_right B₁ B₂)
  by_cases hJwide : (T : ℝ) ^ (1 / 4 + 1 / 1000 : ℝ) ≤ J
  · apply hwide t u v H J T hTw hv hJ huv hambient horient hspan _ _ hJwide
    · exact (mul_le_mul_of_nonneg_left hpoww (Real.rpow_nonneg (by positivity) _)).trans hsideH
    · exact (mul_le_mul_of_nonneg_left hpoww (Real.rpow_nonneg (by positivity) _)).trans hprod
  · have hJupper := (lt_of_not_ge hJwide).le
    by_cases huLarge : (T : ℝ) ^ (1 / 16 : ℝ) ≤ u
    · apply hcritical t u v H J T hTc hu hv hH
        (first_side_lt_step_of_proper hv horient hproper).le huv hambient horient hspan huLarge hJupper
      · exact (mul_le_mul_of_nonneg_left hpowc (Real.rpow_nonneg (by positivity) _)).trans hsideJ
      · exact (mul_le_mul_of_nonneg_left hpowc (Real.rpow_nonneg (by positivity) _)).trans hprod
    · have hpow1 : 1 ≤ (1 + Real.log T) ^ max B₁ B₂ := one_le_pow₀ hΛ1
      have hJplain : (T : ℝ) ^ (1 / 4 : ℝ) ≤ J :=
        (le_mul_of_one_le_right (Real.rpow_nonneg (by positivity) _) hpow1).trans hsideJ
      have hprodplain : (T : ℝ) ^ (3 / 4 : ℝ) ≤ (H : ℝ) * J :=
        (le_mul_of_one_le_right (Real.rpow_nonneg (by positivity) _) hpow1).trans hprod
      exact hsmall t u v H J T hTs hu hH huv hambient horient hspan (lt_of_not_ge huLarge).le
        hJplain hJupper hprodplain

theorem exists_primitive_terminal_unoriented (C : ℝ) (hC : 0 < C) :
    ∃ B : ℕ, 0 < B ∧ ∃ T₀ : ℝ, ∀ (t u v H J T : ℕ), T₀ ≤ (T : ℝ) →
      0 < u → 0 < v → 0 < H → 0 < J → u.Coprime v →
      t + u * H + v * J ≤ T →
      (T : ℝ) ≤ C * ((u * H + v * J : ℕ) : ℝ) →
      (∀ x₁ ≤ H, ∀ y₁ ≤ J, ∀ x₂ ≤ H, ∀ y₂ ≤ J,
        t + u * x₁ + v * y₁ = t + u * x₂ + v * y₂ → x₁ = x₂ ∧ y₁ = y₂) →
      (T : ℝ) ^ (1 / 4 : ℝ) * (1 + Real.log T) ^ B ≤ H →
      (T : ℝ) ^ (1 / 4 : ℝ) * (1 + Real.log T) ^ B ≤ J →
      (T : ℝ) ^ (3 / 4 : ℝ) * (1 + Real.log T) ^ B ≤ (H : ℝ) * J →
      ∃ x ≤ H, ∃ y ≤ J, ∃ z : ℕ, 0 < z ∧ z ^ 2 = t + u * x + v * y := by
  obtain ⟨B, hB, T₀, hterminal⟩ := exists_primitive_terminal C hC
  refine ⟨B, hB, T₀, ?_⟩
  intro t u v H J T hbig hu hv hH hJ huv hambient hspan hproper hsideH hsideJ hprod
  by_cases horient : u * H ≤ v * J
  · exact hterminal t u v H J T hbig hu hv hH hJ huv hambient horient hspan hproper hsideH hsideJ hprod
  · have hambient' : t + v * J + u * H ≤ T := by
      simpa only [Nat.add_assoc, Nat.add_comm (v * J) (u * H)] using hambient
    have hspan' : (T : ℝ) ≤ C * ((v * J + u * H : ℕ) : ℝ) := by
      simpa only [Nat.add_comm (v * J) (u * H)] using hspan
    have hproper' : ∀ x₁ ≤ J, ∀ y₁ ≤ H, ∀ x₂ ≤ J, ∀ y₂ ≤ H,
        t + v * x₁ + u * y₁ = t + v * x₂ + u * y₂ → x₁ = x₂ ∧ y₁ = y₂ := by
      intro x₁ hx₁ y₁ hy₁ x₂ hx₂ y₂ hy₂ heq
      have hh := hproper y₁ hy₁ x₁ hx₁ y₂ hy₂ x₂ hx₂ (by
        simpa only [Nat.add_assoc, Nat.add_comm (v * x₁) (u * y₁),
          Nat.add_comm (v * x₂) (u * y₂)] using heq)
      exact ⟨hh.2, hh.1⟩
    have hprod' : (T : ℝ) ^ (3 / 4 : ℝ) * (1 + Real.log T) ^ B ≤ (J : ℝ) * H := by
      simpa only [mul_comm (J : ℝ) (H : ℝ)] using hprod
    obtain ⟨x, hx, y, hy, z, hz, heq⟩ := hterminal t v u J H T hbig hv hu hJ hH huv.symm
      hambient' (by omega) hspan' hproper' hsideJ hsideH hprod'
    refine ⟨y, hy, x, hx, z, hz, ?_⟩
    simpa only [Nat.add_assoc, Nat.add_comm (v * x) (u * y)] using heq

end Erdos587
