import ErdosProblems.Erdos421.LocalLogarithmicMean
import ErdosProblems.Erdos421.UniformWindowGrid

/-! # A dyadic mean-square bound for actual logarithmic rough windows -/

namespace Erdos421

open MeasureTheory Filter Topology

theorem exists_dyadic_logarithmic_mean_with_grid :
    ∃ K : ℝ, 0 < K ∧ ∀ A : ℝ, ∀ ε τ : ℝ, 0 < ε → ε ≤ 1 → 0 < τ →
      ∀ᶠ X : ℕ in atTop, ∀ D z : ℕ, 0 < D → 2 ≤ z →
        ((z * D ^ 2 : ℕ) : ℝ) ≤ (X : ℝ) ^ (21 / 40 : ℝ) →
        16 * Real.exp 1 + 33 + Real.log (32 / ε) ≤ Real.log D / Real.log z →
        ∀ (N B : ℕ) (δ₁ δ₂ ρ : ℝ), 0 < N → 3 * X ≤ B →
          0 < δ₁ → 0 < δ₂ → δ₁ ≤ ρ → δ₂ ≤ ρ → ρ ≤ 1 / 2 →
          (X : ℝ) ^ (1 / 10 : ℝ) ≤ δ₁ * X → (X : ℝ) ^ (1 / 10 : ℝ) ≤ δ₂ * X →
          (∫ x in (X : ℝ)..2 * X, |logarithmicRoughWindow B z δ₁ (Real.log x) -
            logarithmicRoughWindow B z δ₂ (Real.log x)| ^ 2) ≤
              36 * X * (ε * roughEulerProduct z) ^ 2 + N * τ * X / (Real.log X) ^ A +
                6 * X * (K * (ρ + (X : ℝ)⁻¹ + (N : ℝ)⁻¹)) ^ 2 := by
  obtain ⟨K, hK, hlocal⟩ := exists_local_logarithmic_mean_comparison
  refine ⟨K, hK, ?_⟩
  intro A ε τ hε hε1 hτ
  filter_upwards [eventually_ge_atTop 1, hlocal A ε τ hε hε1 hτ] with X hX hlocalX
  intro D z hD hz hMX hlevel N B δ₁ δ₂ ρ hN hB hδ₁ hδ₂ hδ₁ρ hδ₂ρ hρ hY₁ hY₂
  have hXp : (0 : ℝ) < X := by exact_mod_cast hX
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have hρpos : 0 < ρ := hδ₁.trans_le hδ₁ρ
  let E := K * (ρ + (X : ℝ)⁻¹ + (N : ℝ)⁻¹)
  let f : ℝ → ℝ := fun x ↦ |logarithmicRoughWindow B z δ₁ (Real.log x) -
    logarithmicRoughWindow B z δ₂ (Real.log x)| ^ 2
  have hf : ContinuousOn f (Set.Icc (X : ℝ) (2 * X)) :=
    ((logarithmicRoughWindow_log_continuousOn B z δ₁ hXp).sub
      (logarithmicRoughWindow_log_continuousOn B z δ₂ hXp)).abs.pow 2
  have hbound (j : ℕ) (hj : j < N) :
      (∫ x in windowGrid X N j..windowGrid X N (j + 1), f x) ≤
        (windowGrid X N (j + 1) - windowGrid X N j) *
          (36 * (ε * roughEulerProduct z) ^ 2 + 6 * E ^ 2) + τ * X / (Real.log X) ^ A := by
    let a := windowGrid (X : ℝ) N j
    let b := windowGrid (X : ℝ) N (j + 1)
    have hprop := windowGrid_step_properties hXp hN hj
    have ha : 0 < a := hprop.1
    have hab : a ≤ b := hprop.2.1
    have hba : b ≤ (1 + (N : ℝ)⁻¹) * a := hprop.2.2.1
    have hlen : b - a ≤ X := hprop.2.2.2
    have hXa : (X : ℝ) ≤ a := (windowGrid_bounds hXp.le hN hj.le).1
    have haX : a ≤ 2 * X := (windowGrid_bounds hXp.le hN hj.le).2
    have hbX : b ≤ 2 * X := (windowGrid_bounds hXp.le hN (by omega : j + 1 ≤ N)).2
    have hBreal : 3 * (X : ℝ) ≤ B := by exact_mod_cast hB
    have hcut (δ : ℝ) (hδρ : δ ≤ ρ) : b + δ * a ≤ B := by
      have hda := mul_le_mul_of_nonneg_right (hδρ.trans hρ) ha.le
      nlinarith
    have hm := hlocalX D z hD hz hMX hlevel δ₁ δ₂ ρ a b (N : ℝ)⁻¹ B hδ₁ hδ₂
      hδ₁ρ hδ₂ρ hρ ha (by positivity) hab hba hlen
      (hY₁.trans (mul_le_mul_of_nonneg_left hXa hδ₁.le))
      (hY₂.trans (mul_le_mul_of_nonneg_left hXa hδ₂.le)) (hcut δ₁ hδ₁ρ) (hcut δ₂ hδ₂ρ)
    have hinv : a⁻¹ ≤ (X : ℝ)⁻¹ := by
      simpa only [one_div] using one_div_le_one_div_of_le hXp hXa
    have hE : K * (ρ + a⁻¹ + (N : ℝ)⁻¹) ≤ E :=
      mul_le_mul_of_nonneg_left (by linarith) hK.le
    have hsq := pow_le_pow_left₀ (by positivity : 0 ≤ K * (ρ + a⁻¹ + (N : ℝ)⁻¹)) hE 2
    have herr := mul_le_mul_of_nonneg_left hsq (by positivity : 0 ≤ 6 * (b - a))
    change (∫ x in a..b, f x) ≤ _ at hm ⊢
    nlinarith
  have hb := windowGrid_integral_bound f hXp hN hf hbound
  change (∫ x in (X : ℝ)..2 * X, f x) ≤ _
  apply hb.trans_eq
  dsimp only [E]
  ring

end Erdos421
