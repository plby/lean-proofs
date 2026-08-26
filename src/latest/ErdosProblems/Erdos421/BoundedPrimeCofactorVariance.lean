import ErdosProblems.Erdos421.ProductWindowScaling

/-! # Prime-cofactor variance for coefficients bounded by a fixed constant -/

namespace Erdos421

open MeasureTheory Filter Topology
open scoped SchwartzMap

theorem prime_cofactor_bounded_variance (φ : 𝓢(ℝ, ℂ)) {β e A ε C : ℝ}
    (hβ : 0 < β) (he : 0 < e) (he' : e < 9 / 10) (hA : 0 ≤ A) (hε : 0 < ε) (hC : 0 < C) :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ X : ℕ in atTop,
      4 * Real.pi / (X : ℝ) ^ (9 / 10 - e) ≤ (Real.log X) ^ (-B) ∧
      ∀ M H J : ℕ, 1 ≤ M → 1 ≤ H → M ≤ X → H ≤ X → J ≤ H → M * H = X →
      (X : ℝ) ^ β ≤ H → (H : ℝ) ≤ (X : ℝ) ^ (1 / 5 : ℝ) →
      ∀ (S : Finset ℕ) (a : ℕ → ℂ), (∀ n ∈ S, M ≤ n ∧ n ≤ 2 * M) →
      (∀ n ∈ S, ‖a n‖ ≤ C) → S.card ≤ M →
      ∀ σ ρ₁ ρ₂ : ℝ, 1 ≤ σ →
      4 * Real.pi / (X : ℝ) ^ (9 / 10 - e) ≤ ρ₁ → ρ₁ ≤ (Real.log X) ^ (-B) →
      4 * Real.pi / (X : ℝ) ^ (9 / 10 - e) ≤ ρ₂ → ρ₂ ≤ (Real.log X) ^ (-B) →
      (∫ y : ℝ, ‖scaledProductWindow S (primeBlockSupport H J) a (fun _ ↦ 1) σ φ ρ₁ y -
        scaledProductWindow S (primeBlockSupport H J) a (fun _ ↦ 1) σ φ ρ₂ y‖ ^ 2) ≤
          ε / (Real.log X) ^ A := by
  obtain ⟨B, hB, hmean⟩ := prime_cofactor_two_window_variance φ hβ he he' hA
    (by positivity : 0 < ε / C ^ 2)
  refine ⟨B, hB, ?_⟩
  filter_upwards [hmean] with X hX
  refine ⟨hX.1, ?_⟩
  intro M H J hM hH hMX hHX hJ hprod hHlo hHhi S a hS ha hcard σ ρ₁ ρ₂ hσ
    hρ₁lo hρ₁hi hρ₂lo hρ₂hi
  let a' : ℕ → ℂ := fun n ↦ a n / (C : ℂ)
  have ha' : ∀ n ∈ S, ‖a' n‖ ≤ 1 := by
    intro n hn
    simp only [a', norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hC]
    exact (div_le_one hC).mpr (ha n hn)
  have hb := hX.2 M H J hM hH hMX hHX hJ hprod hHlo hHhi S a' hS ha' hcard
    σ ρ₁ ρ₂ hσ hρ₁lo hρ₁hi hρ₂lo hρ₂hi
  have hCne : (C : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hC.ne'
  have heq : a = fun n ↦ (C : ℂ) * a' n := by
    funext n
    dsimp only [a']
    field_simp
  have hscale (ρ y : ℝ) : scaledProductWindow S (primeBlockSupport H J) a
      (fun _ ↦ 1) σ φ ρ y = (C : ℂ) * scaledProductWindow S (primeBlockSupport H J) a'
        (fun _ ↦ 1) σ φ ρ y := by
    conv_lhs => rw [heq]
    exact scaledProductWindow_const_mul _ _ _ _ _ _ _ _ _
  calc
    _ = C ^ 2 * (∫ y : ℝ, ‖scaledProductWindow S (primeBlockSupport H J) a' (fun _ ↦ 1)
        σ φ ρ₁ y - scaledProductWindow S (primeBlockSupport H J) a' (fun _ ↦ 1) σ φ ρ₂ y‖ ^ 2) := by
      simp_rw [hscale, ← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hC, mul_pow]
      rw [integral_const_mul]
    _ ≤ C ^ 2 * (ε / C ^ 2 / (Real.log X) ^ A) :=
      mul_le_mul_of_nonneg_left hb (sq_nonneg C)
    _ = _ := by field_simp

end Erdos421
