import ErdosProblems.Erdos421.AdditiveRoughAsymptotic
import ErdosProblems.Erdos421.LogarithmicRoughWindows

/-! # Unconditional asymptotics for the actual logarithmic rough window -/

namespace Erdos421

theorem exists_logarithmicRoughWindow_asymptotic :
    ∃ C > 0, ∃ K > 0, ∀ n : ℕ, ∀ A ε : ℝ, 0 ≤ A → 0 < ε → ∃ X₀ > 1,
      ∀ x : ℝ, X₀ ≤ x → ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 2 → ∀ N z : ℕ,
        2 ≤ z → (z : ℝ) ^ 2 ≤ x → (1 + δ) * x ≤ (z : ℝ) ^ (n + 3) →
        (1 + δ) * x ≤ (N : ℝ) + 1 →
        |logarithmicRoughWindow N z δ (Real.log x) -
          finiteBuchstab (n + 1) (Real.log x / Real.log z) / Real.log z| ≤
          K * (δ + x⁻¹) + C * ε / (δ * (Real.log x) ^ A) +
            C * (roughCountErrorConstant (n + 1) + ((n : ℝ) + 3) ^ 2) * δ /
              (Real.log x) ^ 2 := by
  obtain ⟨C, hC, hadd⟩ := exists_additiveRoughWindow_asymptotic
  obtain ⟨K, hK, hcompare⟩ := exists_logarithmicRoughWindow_additive_comparison
  refine ⟨C, hC, K, hK, ?_⟩
  intro n A ε hA hε
  obtain ⟨X₀, hX₀, hwindow⟩ := hadd n A ε hA hε
  refine ⟨X₀, hX₀, ?_⟩
  intro x hx δ hδ hδhi N z hz hzsq hpow hN
  have hx1 := hX₀.trans_le hx
  have hxp : 0 < x := by linarith
  have hLx := Real.log_pos hx1
  have hY : 0 < δ * x := mul_pos hδ hxp
  have hYx : δ * x ≤ x := by nlinarith
  have hlength : x + δ * x = (1 + δ) * x := by ring
  have ha := hwindow x hx (δ * x) hY hYx N z hz hzsq
    (by rwa [hlength]) (by rwa [hlength])
  have ha' : |additiveRoughWindow N z (δ * x) x -
      finiteBuchstab (n + 1) (Real.log x / Real.log z) / Real.log z| ≤
      C * ε / (δ * (Real.log x) ^ A) +
        C * (roughCountErrorConstant (n + 1) + ((n : ℝ) + 3) ^ 2) * δ / (Real.log x) ^ 2 :=
    ha.trans_eq (by field_simp)
  have hc := hcompare N z δ x hδ hδhi hxp
  calc
    _ = |(logarithmicRoughWindow N z δ (Real.log x) - additiveRoughWindow N z (δ * x) x) +
        (additiveRoughWindow N z (δ * x) x -
          finiteBuchstab (n + 1) (Real.log x / Real.log z) / Real.log z)| := by congr 1; ring
    _ ≤ |logarithmicRoughWindow N z δ (Real.log x) - additiveRoughWindow N z (δ * x) x| +
        |additiveRoughWindow N z (δ * x) x -
          finiteBuchstab (n + 1) (Real.log x / Real.log z) / Real.log z| := abs_add_le _ _
    _ ≤ _ := add_le_add hc ha'
    _ = _ := by ring

end Erdos421
