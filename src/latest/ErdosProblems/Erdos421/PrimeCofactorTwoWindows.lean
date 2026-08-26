import ErdosProblems.Erdos421.PrimeCofactorSmoothVariance

/-! # Comparing any two admissible prime-cofactor windows -/

namespace Erdos421

open MeasureTheory Filter Topology
open scoped SchwartzMap

theorem schwartz_difference_energy_triangle (f g h : 𝓢(ℝ, ℂ)) :
    (∫ x : ℝ, ‖f x - g x‖ ^ 2) ≤
      2 * (∫ x : ℝ, ‖h x - f x‖ ^ 2) + 2 * (∫ x : ℝ, ‖h x - g x‖ ^ 2) := by
  have hf : Integrable (fun x : ℝ ↦ ‖f x - g x‖ ^ 2) :=
    ((f - g).memLp 2).integrable_norm_pow (by decide : 2 ≠ 0)
  have hhf : Integrable (fun x : ℝ ↦ ‖h x - f x‖ ^ 2) :=
    ((h - f).memLp 2).integrable_norm_pow (by decide : 2 ≠ 0)
  have hhg : Integrable (fun x : ℝ ↦ ‖h x - g x‖ ^ 2) :=
    ((h - g).memLp 2).integrable_norm_pow (by decide : 2 ≠ 0)
  have hpoint (x : ℝ) :
      ‖f x - g x‖ ^ 2 ≤ 2 * ‖h x - f x‖ ^ 2 + 2 * ‖h x - g x‖ ^ 2 := by
    have hb : ‖f x - g x‖ ≤ ‖h x - f x‖ + ‖h x - g x‖ := by
      calc
        _ = ‖(f x - h x) + (h x - g x)‖ := by rw [sub_add_sub_cancel]
        _ ≤ ‖f x - h x‖ + ‖h x - g x‖ := norm_add_le _ _
        _ = _ := by rw [norm_sub_rev (f x) (h x)]
    have hs := pow_le_pow_left₀ (norm_nonneg _) hb 2
    nlinarith [sq_nonneg (‖h x - f x‖ - ‖h x - g x‖)]
  have hi := integral_mono hf ((hhf.const_mul 2).add (hhg.const_mul 2)) hpoint
  simp only [Pi.add_apply] at hi
  rw [integral_add (hhf.const_mul 2) (hhg.const_mul 2),
    integral_const_mul, integral_const_mul] at hi
  exact hi

theorem prime_cofactor_two_window_variance (φ : 𝓢(ℝ, ℂ)) {β e A ε : ℝ}
    (hβ : 0 < β) (he : 0 < e) (he' : e < 9 / 10) (hA : 0 ≤ A) (hε : 0 < ε) :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ X : ℕ in atTop,
      4 * Real.pi / (X : ℝ) ^ (9 / 10 - e) ≤ (Real.log X) ^ (-B) ∧
      ∀ M H J : ℕ, 1 ≤ M → 1 ≤ H → M ≤ X → H ≤ X → J ≤ H → M * H = X →
      (X : ℝ) ^ β ≤ H → (H : ℝ) ≤ (X : ℝ) ^ (1 / 5 : ℝ) →
      ∀ (S : Finset ℕ) (a : ℕ → ℂ), (∀ n ∈ S, M ≤ n ∧ n ≤ 2 * M) →
      (∀ n ∈ S, ‖a n‖ ≤ 1) → S.card ≤ M →
      ∀ σ ρ₁ ρ₂ : ℝ, 1 ≤ σ →
      4 * Real.pi / (X : ℝ) ^ (9 / 10 - e) ≤ ρ₁ → ρ₁ ≤ (Real.log X) ^ (-B) →
      4 * Real.pi / (X : ℝ) ^ (9 / 10 - e) ≤ ρ₂ → ρ₂ ≤ (Real.log X) ^ (-B) →
      (∫ y : ℝ, ‖scaledProductWindow S (primeBlockSupport H J) a (fun _ ↦ 1) σ φ ρ₁ y -
        scaledProductWindow S (primeBlockSupport H J) a (fun _ ↦ 1) σ φ ρ₂ y‖ ^ 2) ≤
          ε / (Real.log X) ^ A := by
  obtain ⟨B, hB, hmean⟩ := prime_cofactor_smooth_variance φ hβ he he' hA
    (by positivity : 0 < ε / 4)
  refine ⟨B, hB, ?_⟩
  filter_upwards [hmean, eventually_ge_atTop 1] with X hmeanX hX
  refine ⟨hmeanX.1, ?_⟩
  intro M H J hM hH hMX hHX hJ hprod hHlo hHhi S a hS ha hcard σ ρ₁ ρ₂ hσ
    hρ₁lo hρ₁hi hρ₂lo hρ₂hi
  have hXp : (0 : ℝ) < X := by exact_mod_cast hX
  let δ := 4 * Real.pi / (X : ℝ) ^ (9 / 10 - e)
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  have hρ₁ : 0 < ρ₁ := hδ.trans_le hρ₁lo
  have hρ₂ : 0 < ρ₂ := hδ.trans_le hρ₂lo
  have hm₁ := hmeanX.2 M H J hM hH hMX hHX hJ hprod hHlo hHhi S a hS ha hcard
    σ ρ₁ hσ hρ₁lo hρ₁hi
  have hm₂ := hmeanX.2 M H J hM hH hMX hHX hJ hprod hHlo hHhi S a hS ha hcard
    σ ρ₂ hσ hρ₂lo hρ₂hi
  have hb := schwartz_difference_energy_triangle
    (schwartzProductWindow S (primeBlockSupport H J) a (fun _ ↦ 1) σ
      (normalizedSchwartzScale ρ₁ hρ₁ φ))
    (schwartzProductWindow S (primeBlockSupport H J) a (fun _ ↦ 1) σ
      (normalizedSchwartzScale ρ₂ hρ₂ φ))
    (schwartzProductWindow S (primeBlockSupport H J) a (fun _ ↦ 1) σ
      (normalizedSchwartzScale δ hδ φ))
  simp only [schwartzProductWindow_normalized_apply, δ] at hb
  apply hb.trans
  calc
    _ ≤ 2 * (ε / 4 / (Real.log X) ^ A) + 2 * (ε / 4 / (Real.log X) ^ A) :=
      add_le_add (mul_le_mul_of_nonneg_left hm₁ (by norm_num))
        (mul_le_mul_of_nonneg_left hm₂ (by norm_num))
    _ = _ := by ring

end Erdos421
