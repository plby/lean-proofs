import ErdosProblems.Erdos421.AdditiveKernelIdentity

/-! # Unconditional asymptotics for the actual smooth additive rough window -/

namespace Erdos421

theorem exists_additiveRoughWindow_asymptotic :
    ∃ C > 0, ∀ n : ℕ, ∀ A ε : ℝ, 0 ≤ A → 0 < ε → ∃ X₀ > 1,
      ∀ x : ℝ, X₀ ≤ x → ∀ Y : ℝ, 0 < Y → Y ≤ x → ∀ N z : ℕ,
        2 ≤ z → (z : ℝ) ^ 2 ≤ x → x + Y ≤ (z : ℝ) ^ (n + 3) →
        x + Y ≤ (N : ℝ) + 1 →
        |additiveRoughWindow N z Y x -
          finiteBuchstab (n + 1) (Real.log x / Real.log z) / Real.log z| ≤
          C * ε * x / (Y * (Real.log x) ^ A) +
            C * (roughCountErrorConstant (n + 1) + ((n : ℝ) + 3) ^ 2) * Y /
              (x * (Real.log x) ^ 2) := by
  obtain ⟨C, hC, hderiv⟩ := exists_oneSidedRealWindow_deriv_bound
  refine ⟨C, hC, ?_⟩
  intro n A ε hA hε
  obtain ⟨X₀, hX₀, hweight⟩ := rough_weighted_sum_asymptotic n hA hε
  refine ⟨X₀, hX₀, ?_⟩
  intro x hx Y hY hYx N z hz hzsq hpow hN
  have hx1 := hX₀.trans_le hx
  have hxp : 0 < x := by linarith
  have hLx := Real.log_pos hx1
  have hD : 0 ≤ roughCountErrorConstant (n + 1) + ((n : ℝ) + 3) ^ 2 :=
    add_nonneg (roughCountErrorConstant_nonneg _) (sq_nonneg _)
  have hw := hweight x hx Y hY.le hYx z hz hzsq hpow (realAdditiveKernel Y x)
    (fun t _ ↦ (realAdditiveKernel_hasDerivAt hY x t).differentiableAt)
    (realAdditiveKernel_deriv_continuous Y x).continuousOn
  rw [realAdditiveKernel_integral hY x, mul_one] at hw
  rw [additiveRoughWindow_interval_sum hY hxp.le hN z]
  calc
    _ ≤ _ := hw
    _ ≤ (ε * x / (Real.log x) ^ A +
        (roughCountErrorConstant (n + 1) + ((n : ℝ) + 3) ^ 2) * Y ^ 2 /
          (x * (Real.log x) ^ 2)) * (C / Y) :=
      mul_le_mul_of_nonneg_left (realAdditiveKernel_variation_le hderiv hY x) (by positivity)
    _ = _ := by field_simp

end Erdos421
