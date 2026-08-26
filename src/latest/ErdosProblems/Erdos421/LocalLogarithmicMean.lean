import ErdosProblems.Erdos421.LocalLogarithmicWindows
import ErdosProblems.Erdos421.RoughWindowLengthMean

/-! # Mean-square comparison of logarithmic rough windows on a short block -/

namespace Erdos421

open MeasureTheory Filter Topology

theorem interval_square_comparison_of_error (f₁ f₂ g₁ g₂ : ℝ → ℝ) {a b E : ℝ}
    (hab : a ≤ b) (_hE : 0 ≤ E)
    (hf : IntervalIntegrable (fun x ↦ |f₁ x - f₂ x| ^ 2) volume a b)
    (hg : IntervalIntegrable (fun x ↦ |g₁ x - g₂ x| ^ 2) volume a b)
    (h₁ : ∀ x ∈ Set.Icc a b, |f₁ x - g₁ x| ≤ E)
    (h₂ : ∀ x ∈ Set.Icc a b, |f₂ x - g₂ x| ≤ E) :
    (∫ x in a..b, |f₁ x - f₂ x| ^ 2) ≤
      3 * (∫ x in a..b, |g₁ x - g₂ x| ^ 2) + 6 * (b - a) * E ^ 2 := by
  have hGI : IntervalIntegrable (fun x ↦ 3 * |g₁ x - g₂ x| ^ 2) volume a b := hg.const_mul 3
  have hEI : IntervalIntegrable (fun _ : ℝ ↦ 6 * E ^ 2) volume a b := intervalIntegrable_const
  have hpoint (x : ℝ) (hx : x ∈ Set.Icc a b) :
      |f₁ x - f₂ x| ^ 2 ≤ 3 * |g₁ x - g₂ x| ^ 2 + 6 * E ^ 2 := by
    have ht₁ := abs_sub_le (f₁ x) (g₁ x) (f₂ x)
    have ht₂ := abs_sub_le (g₁ x) (g₂ x) (f₂ x)
    rw [abs_sub_comm (g₂ x) (f₂ x)] at ht₂
    have hb : |f₁ x - f₂ x| ≤ |g₁ x - g₂ x| + 2 * E := by
      linarith [h₁ x hx, h₂ x hx]
    have hs := pow_le_pow_left₀ (abs_nonneg _) hb 2
    nlinarith [sq_nonneg (|g₁ x - g₂ x| - E)]
  have hi := intervalIntegral.integral_mono_on hab hf (hGI.add hEI) hpoint
  rw [intervalIntegral.integral_add hGI hEI, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const] at hi
  simp only [smul_eq_mul] at hi
  nlinarith

theorem logarithmicRoughWindow_log_continuousOn (B z : ℕ) (δ : ℝ) {a b : ℝ} (ha : 0 < a) :
    ContinuousOn (fun x ↦ logarithmicRoughWindow B z δ (Real.log x)) (Set.Icc a b) := by
  apply (logarithmicRoughWindow_continuous B z δ).comp_continuousOn
  exact continuousOn_id.log (fun x hx ↦ (ha.trans_le hx.1).ne')

theorem exists_local_logarithmic_mean_comparison :
    ∃ K : ℝ, 0 < K ∧ ∀ A : ℝ, ∀ ε τ : ℝ, 0 < ε → ε ≤ 1 → 0 < τ →
      ∀ᶠ X : ℕ in atTop, ∀ D z : ℕ, 0 < D → 2 ≤ z →
        ((z * D ^ 2 : ℕ) : ℝ) ≤ (X : ℝ) ^ (21 / 40 : ℝ) →
        16 * Real.exp 1 + 33 + Real.log (32 / ε) ≤ Real.log D / Real.log z →
        ∀ (δ₁ δ₂ ρ a b η : ℝ) (B : ℕ),
          0 < δ₁ → 0 < δ₂ → δ₁ ≤ ρ → δ₂ ≤ ρ → ρ ≤ 1 / 2 →
          0 < a → 0 ≤ η → a ≤ b → b ≤ (1 + η) * a → b - a ≤ X →
          (X : ℝ) ^ (1 / 10 : ℝ) ≤ δ₁ * a → (X : ℝ) ^ (1 / 10 : ℝ) ≤ δ₂ * a →
          b + δ₁ * a ≤ B → b + δ₂ * a ≤ B →
          (∫ x in a..b, |logarithmicRoughWindow B z δ₁ (Real.log x) -
            logarithmicRoughWindow B z δ₂ (Real.log x)| ^ 2) ≤
              36 * (b - a) * (ε * roughEulerProduct z) ^ 2 + τ * X / (Real.log X) ^ A +
                6 * (b - a) * (K * (ρ + a⁻¹ + η)) ^ 2 := by
  obtain ⟨K, hK, hkernel⟩ := exists_local_logarithmic_window_comparison
  refine ⟨K, hK, ?_⟩
  intro A ε τ hε hε1 hτ
  filter_upwards [eventually_ge_atTop 1,
    additiveRoughWindow_length_comparison A hε hε1 (by positivity : 0 < τ / 3)] with X hX hmean
  intro D z hD hz hMX hlevel δ₁ δ₂ ρ a b η B hδ₁ hδ₂ hδ₁ρ hδ₂ρ hρ ha hη hab hba hlen
    hY₁ hY₂ hB₁ hB₂
  have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hlength : 1 ≤ (X : ℝ) ^ (1 / 10 : ℝ) := Real.one_le_rpow hX1 (by norm_num)
  have hbound (δ : ℝ) (hδ : 0 < δ) (hδρ : δ ≤ ρ)
      (hY : (X : ℝ) ^ (1 / 10 : ℝ) ≤ δ * a) (x : ℝ) (hx : x ∈ Set.Icc a b) :
      |logarithmicRoughWindow B z δ (Real.log x) - additiveRoughWindow B z (δ * a) x| ≤
        K * (ρ + a⁻¹ + η) := by
    apply (hkernel B z δ a η x hδ (hδρ.trans hρ) ha hη hx.1 (hx.2.trans hba)
      (hlength.trans hY)).trans
    exact mul_le_mul_of_nonneg_left (by linarith) hK.le
  have hFI : IntervalIntegrable (fun x ↦ |logarithmicRoughWindow B z δ₁ (Real.log x) -
      logarithmicRoughWindow B z δ₂ (Real.log x)| ^ 2) volume a b :=
    (((logarithmicRoughWindow_log_continuousOn B z δ₁ ha).sub
      (logarithmicRoughWindow_log_continuousOn B z δ₂ ha)).abs.pow 2).intervalIntegrable_of_Icc hab
  have hGI : IntervalIntegrable (fun x ↦ |additiveRoughWindow B z (δ₁ * a) x -
      additiveRoughWindow B z (δ₂ * a) x| ^ 2) volume a b :=
    (((additiveRoughWindow_continuous B z (δ₁ * a)).sub
      (additiveRoughWindow_continuous B z (δ₂ * a))).abs.pow 2).intervalIntegrable a b
  have hE : 0 ≤ K * (ρ + a⁻¹ + η) := by have hρpos := hδ₁.trans_le hδ₁ρ; positivity
  have hb := interval_square_comparison_of_error
    (fun x ↦ logarithmicRoughWindow B z δ₁ (Real.log x))
    (fun x ↦ logarithmicRoughWindow B z δ₂ (Real.log x))
    (additiveRoughWindow B z (δ₁ * a)) (additiveRoughWindow B z (δ₂ * a)) hab hE hFI hGI
    (hbound δ₁ hδ₁ hδ₁ρ hY₁) (hbound δ₂ hδ₂ hδ₂ρ hY₂)
  have hm := hmean D z hD hz hMX hlevel (δ₁ * a) (δ₂ * a) a b B hY₁ hY₂ ha.le hab hlen hB₁ hB₂
  apply hb.trans
  calc
    _ ≤ 3 * (12 * (b - a) * (ε * roughEulerProduct z) ^ 2 + τ / 3 * X / (Real.log X) ^ A) +
        6 * (b - a) * (K * (ρ + a⁻¹ + η)) ^ 2 :=
      add_le_add (mul_le_mul_of_nonneg_left hm (by norm_num)) le_rfl
    _ = _ := by ring

end Erdos421
