import ErdosProblems.Erdos421.DyadicCofactorMean
import ErdosProblems.Erdos421.LogarithmicMeasureMean

/-! # Logarithmic measure for the actual cofactor-window comparison -/

namespace Erdos421

open MeasureTheory Filter Topology

theorem exists_logarithmic_cofactor_variance_with_grid {k : ℕ} (hk : 0 < k) :
    ∃ K : ℝ, 0 < K ∧ ∀ A : ℝ, ∀ ε τ : ℝ, 0 < ε → ε ≤ 1 → 0 < τ →
      ∀ᶠ X : ℕ in atTop, ∀ Q D z w : ℕ, 0 < Q → 0 < D → 2 ≤ z → 0 < w →
        Q * (z * D ^ 2) < w ^ k →
        ((Q * (z * D ^ 2) : ℕ) : ℝ) ≤ (X : ℝ) ^ (21 / 40 : ℝ) →
        16 * Real.exp 1 + 33 + Real.log (32 / ε) ≤ Real.log D / Real.log z →
        ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime ∧ w ≤ p ∧ p ≤ Q) →
        ∀ (N B : ℕ) (δ₁ δ₂ ρ : ℝ), B < w ^ k → 0 < N → 3 * X ≤ B →
          0 < δ₁ → 0 < δ₂ → δ₁ ≤ ρ → δ₂ ≤ ρ → ρ ≤ 1 / 2 →
          (X : ℝ) ^ (1 / 10 : ℝ) ≤ δ₁ * X → (X : ℝ) ^ (1 / 10 : ℝ) ≤ δ₂ * X →
          (∫ y in Real.log (X : ℝ)..Real.log (2 * X : ℝ),
            |logarithmicPrimeCofactorWindow P B z δ₁ y -
              logarithmicPrimeCofactorWindow P B z δ₂ y| ^ 2) ≤
              36 * (ε * (∑ p ∈ P, (p : ℝ)⁻¹) * roughEulerProduct z) ^ 2 +
                N * τ / (Real.log X) ^ A +
                6 * (K * (ρ + (X : ℝ)⁻¹ + (N : ℝ)⁻¹)) ^ 2 := by
  obtain ⟨K, hK, hmean⟩ := exists_dyadic_logarithmic_cofactor_mean_with_grid hk
  refine ⟨K, hK, ?_⟩
  intro A ε τ hε hε1 hτ
  filter_upwards [eventually_ge_atTop 1, hmean A ε τ hε hε1 hτ] with X hX hmeanX
  intro Q D z w hQ hD hz hw hcut hMX hlevel P hP N B δ₁ δ₂ ρ hBw hN hB
    hδ₁ hδ₂ hδ₁ρ hδ₂ρ hρ hY₁ hY₂
  have hXp : (0 : ℝ) < X := by exact_mod_cast hX
  let g : ℝ → ℝ := fun y ↦
    |logarithmicPrimeCofactorWindow P B z δ₁ y - logarithmicPrimeCofactorWindow P B z δ₂ y| ^ 2
  have hg : Continuous g := ((logarithmicPrimeCofactorWindow_continuous P B z δ₁).sub
    (logarithmicPrimeCofactorWindow_continuous P B z δ₂)).abs.pow 2
  have hb := logarithmic_integral_le g hg (fun y ↦ sq_nonneg _) hXp
  have hm := hmeanX Q D z w hQ hD hz hw hcut hMX hlevel P hP N B δ₁ δ₂ ρ
    hBw hN hB hδ₁ hδ₂ hδ₁ρ hδ₂ρ hρ hY₁ hY₂
  apply hb.trans
  apply le_trans (mul_le_mul_of_nonneg_left hm (inv_nonneg.mpr hXp.le))
  exact le_of_eq (by field_simp)

end Erdos421
