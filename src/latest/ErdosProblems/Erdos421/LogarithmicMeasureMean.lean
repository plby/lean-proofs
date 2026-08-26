import ErdosProblems.Erdos421.DyadicLogarithmicMean

/-! # Passing the dyadic mean bound to logarithmic measure -/

namespace Erdos421

open MeasureTheory Filter Topology

theorem logarithmic_integral_le (g : ℝ → ℝ) (hg : Continuous g) (hg0 : ∀ y, 0 ≤ g y)
    {X : ℝ} (hX : 0 < X) :
    (∫ y in Real.log X..Real.log (2 * X), g y) ≤
      X⁻¹ * ∫ x in X..2 * X, g (Real.log x) := by
  have hXX : X ≤ 2 * X := by linarith
  have hne : ∀ x ∈ Set.uIcc X (2 * X), x ≠ 0 := by
    intro x hx
    rw [Set.uIcc_of_le hXX] at hx
    exact (hX.trans_le hx.1).ne'
  have hderiv : ∀ x ∈ Set.uIcc X (2 * X), HasDerivAt Real.log x⁻¹ x :=
    fun x hx ↦ Real.hasDerivAt_log (hne x hx)
  have hinv : ContinuousOn (fun x : ℝ ↦ x⁻¹) (Set.uIcc X (2 * X)) :=
    continuousOn_id.inv₀ hne
  have hlog : ContinuousOn Real.log (Set.uIcc X (2 * X)) := continuousOn_id.log hne
  have hcomp := hg.comp_continuousOn hlog
  have hsub := intervalIntegral.integral_comp_mul_deriv hderiv hinv hg
  change (∫ x in X..2 * X, g (Real.log x) * x⁻¹) =
    ∫ y in Real.log X..Real.log (2 * X), g y at hsub
  rw [← hsub]
  have hright : IntervalIntegrable (fun x ↦ X⁻¹ * g (Real.log x)) volume X (2 * X) :=
    (continuousOn_const.mul hcomp).intervalIntegrable
  have hb := intervalIntegral.integral_mono_on (μ := volume) hXX
    ((hcomp.mul hinv).intervalIntegrable) hright (fun x hx ↦ ?_)
  · rw [intervalIntegral.integral_const_mul] at hb
    exact hb
  · have hxX : X ≤ x := hx.1
    have hix : x⁻¹ ≤ X⁻¹ := by
      simpa only [one_div] using one_div_le_one_div_of_le hX hxX
    simpa only [Pi.mul_apply, Function.comp_apply, mul_comm] using
      mul_le_mul_of_nonneg_left hix (hg0 (Real.log x))

theorem exists_logarithmic_variance_with_grid :
    ∃ K : ℝ, 0 < K ∧ ∀ A : ℝ, ∀ ε τ : ℝ, 0 < ε → ε ≤ 1 → 0 < τ →
      ∀ᶠ X : ℕ in atTop, ∀ D z : ℕ, 0 < D → 2 ≤ z →
        ((z * D ^ 2 : ℕ) : ℝ) ≤ (X : ℝ) ^ (21 / 40 : ℝ) →
        16 * Real.exp 1 + 33 + Real.log (32 / ε) ≤ Real.log D / Real.log z →
        ∀ (N B : ℕ) (δ₁ δ₂ ρ : ℝ), 0 < N → 3 * X ≤ B →
          0 < δ₁ → 0 < δ₂ → δ₁ ≤ ρ → δ₂ ≤ ρ → ρ ≤ 1 / 2 →
          (X : ℝ) ^ (1 / 10 : ℝ) ≤ δ₁ * X → (X : ℝ) ^ (1 / 10 : ℝ) ≤ δ₂ * X →
          (∫ y in Real.log (X : ℝ)..Real.log (2 * X : ℝ),
            |logarithmicRoughWindow B z δ₁ y - logarithmicRoughWindow B z δ₂ y| ^ 2) ≤
              36 * (ε * roughEulerProduct z) ^ 2 + N * τ / (Real.log X) ^ A +
                6 * (K * (ρ + (X : ℝ)⁻¹ + (N : ℝ)⁻¹)) ^ 2 := by
  obtain ⟨K, hK, hmean⟩ := exists_dyadic_logarithmic_mean_with_grid
  refine ⟨K, hK, ?_⟩
  intro A ε τ hε hε1 hτ
  filter_upwards [eventually_ge_atTop 1, hmean A ε τ hε hε1 hτ] with X hX hmeanX
  intro D z hD hz hMX hlevel N B δ₁ δ₂ ρ hN hB hδ₁ hδ₂ hδ₁ρ hδ₂ρ hρ hY₁ hY₂
  have hXp : (0 : ℝ) < X := by exact_mod_cast hX
  let g : ℝ → ℝ := fun y ↦
    |logarithmicRoughWindow B z δ₁ y - logarithmicRoughWindow B z δ₂ y| ^ 2
  have hg : Continuous g := ((logarithmicRoughWindow_continuous B z δ₁).sub
    (logarithmicRoughWindow_continuous B z δ₂)).abs.pow 2
  have hb := logarithmic_integral_le g hg (fun y ↦ sq_nonneg _) hXp
  have hm := hmeanX D z hD hz hMX hlevel N B δ₁ δ₂ ρ hN hB hδ₁ hδ₂ hδ₁ρ hδ₂ρ hρ hY₁ hY₂
  apply hb.trans
  apply le_trans (mul_le_mul_of_nonneg_left hm (inv_nonneg.mpr hXp.le))
  exact le_of_eq (by field_simp)

end Erdos421
