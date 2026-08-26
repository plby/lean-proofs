import ErdosProblems.Erdos421.RoughWindowMeanSquare

/-! # Comparing two actual smooth rough-number windows -/

namespace Erdos421

open MeasureTheory Filter Topology

theorem continuous_interval_square_difference_le (f g : ℝ → ℝ) (hf : Continuous f)
    (hg : Continuous g) (c : ℝ) {u v : ℝ} (huv : u ≤ v) :
    (∫ x in u..v, |f x - g x| ^ 2) ≤
      2 * (∫ x in u..v, |f x - c| ^ 2) + 2 * (∫ x in u..v, |g x - c| ^ 2) := by
  have hF : IntervalIntegrable (fun x ↦ 2 * |f x - c| ^ 2) volume u v :=
    (continuous_const.mul ((hf.sub continuous_const).abs.pow 2)).intervalIntegrable u v
  have hG : IntervalIntegrable (fun x ↦ 2 * |g x - c| ^ 2) volume u v :=
    (continuous_const.mul ((hg.sub continuous_const).abs.pow 2)).intervalIntegrable u v
  have hb := intervalIntegral.integral_mono_on huv
    (((hf.sub hg).abs.pow 2).intervalIntegrable u v) (hF.add hG) (fun x _ ↦ ?_)
  · rw [intervalIntegral.integral_add hF hG, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul] at hb
    exact hb
  · change |f x - g x| ^ 2 ≤ 2 * |f x - c| ^ 2 + 2 * |g x - c| ^ 2
    simp only [sq_abs]
    nlinarith [sq_nonneg (f x + g x - 2 * c)]

theorem additiveRoughWindow_comparison (A : ℝ) {ε τ : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hτ : 0 < τ) :
    ∀ᶠ X : ℕ in atTop, ∀ D z : ℕ, 0 < D → 2 ≤ z →
      ((z * D ^ 2 : ℕ) : ℝ) ≤ (X : ℝ) ^ (21 / 40 : ℝ) →
      16 * Real.exp 1 + 33 + Real.log (32 / ε) ≤ Real.log D / Real.log z →
      ∀ (Y₁ Y₂ u v : ℝ) (B : ℕ), (X : ℝ) ^ (1 / 10 : ℝ) ≤ Y₁ →
      (X : ℝ) ^ (1 / 10 : ℝ) ≤ Y₂ →
      0 ≤ u → u ≤ v → v - u ≤ X → v + Y₁ ≤ B → v + Y₂ ≤ B →
      (∫ x in u..v, |additiveRoughWindow B z Y₁ x - additiveRoughWindow B z Y₂ x| ^ 2) ≤
        12 * X * (ε * roughEulerProduct z) ^ 2 + τ * X / (Real.log X) ^ A := by
  filter_upwards [additiveRoughWindow_mean_square A hε hε1 (by positivity : 0 < τ / 4)] with X hX
  intro D z hD hz hMX hlevel Y₁ Y₂ u v B hY₁ hY₂ hu huv hlen hB₁ hB₂
  have h₁ := hX D z hD hz hMX hlevel Y₁ u v B hY₁ hu huv hlen hB₁
  have h₂ := hX D z hD hz hMX hlevel Y₂ u v B hY₂ hu huv hlen hB₂
  have hb := continuous_interval_square_difference_le (additiveRoughWindow B z Y₁)
    (additiveRoughWindow B z Y₂) (additiveRoughWindow_continuous B z Y₁)
    (additiveRoughWindow_continuous B z Y₂) (roughEulerProduct z) huv
  apply hb.trans
  calc
    _ ≤ 2 * (3 * X * (ε * roughEulerProduct z) ^ 2 + τ / 4 * X / (Real.log X) ^ A) +
        2 * (3 * X * (ε * roughEulerProduct z) ^ 2 + τ / 4 * X / (Real.log X) ^ A) :=
      add_le_add (mul_le_mul_of_nonneg_left h₁ (by norm_num))
        (mul_le_mul_of_nonneg_left h₂ (by norm_num))
    _ = _ := by ring

end Erdos421
