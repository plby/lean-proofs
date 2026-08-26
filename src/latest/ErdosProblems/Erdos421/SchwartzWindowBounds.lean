import ErdosProblems.Erdos421.SchwartzWindowScaling
import Mathlib.Analysis.Calculus.MeanValue

/-! # Uniform decay and continuity estimates for smooth-window Fourier multipliers -/

namespace Erdos421

open Complex FourierTransform
open scoped SchwartzMap

theorem exists_schwartz_fourier_bounds (φ : 𝓢(ℝ, ℂ)) :
    ∃ C > 0, (∀ t : ℝ, ‖𝓕 φ t‖ ≤ C) ∧
      (∀ t : ℝ, |t| * ‖𝓕 φ t‖ ≤ C) ∧
      (∀ s t : ℝ, ‖𝓕 φ s - 𝓕 φ t‖ ≤ C * |s - t|) := by
  let ψ : 𝓢(ℝ, ℂ) := 𝓕 φ
  let p₀ : ℝ := SchwartzMap.seminorm ℝ 0 0 ψ
  let p₁ : ℝ := SchwartzMap.seminorm ℝ 1 0 ψ
  let p₂ : ℝ := SchwartzMap.seminorm ℝ 0 1 ψ
  have h₀ : 0 ≤ p₀ := apply_nonneg _ _
  have h₁ : 0 ≤ p₁ := apply_nonneg _ _
  have h₂ : 0 ≤ p₂ := apply_nonneg _ _
  let C := 1 + p₀ + p₁ + p₂
  have hC : 0 < C := by dsimp only [C]; linarith
  have hp₀ : p₀ ≤ C := by dsimp only [C]; linarith
  have hp₁ : p₁ ≤ C := by dsimp only [C]; linarith
  have hp₂ : p₂ ≤ C := by dsimp only [C]; linarith
  have hnorm : ∀ t : ℝ, ‖ψ t‖ ≤ C := by
    intro t
    have h := SchwartzMap.le_seminorm' ℝ 0 0 ψ t
    simp only [pow_zero, iteratedDeriv_zero, one_mul] at h
    exact h.trans hp₀
  have hdecay : ∀ t : ℝ, |t| * ‖ψ t‖ ≤ C := by
    intro t
    have h := SchwartzMap.le_seminorm' ℝ 1 0 ψ t
    simp only [pow_one, iteratedDeriv_zero] at h
    exact h.trans hp₁
  have hderiv : ∀ t : ℝ, ‖deriv (ψ : ℝ → ℂ) t‖ ≤ C := by
    intro t
    have h := SchwartzMap.le_seminorm' ℝ 0 1 ψ t
    simp only [pow_zero, iteratedDeriv_one, one_mul] at h
    exact h.trans hp₂
  refine ⟨C, hC, hnorm, hdecay, ?_⟩
  intro s t
  have hb := Convex.norm_image_sub_le_of_norm_deriv_le (𝕜 := ℝ) (s := Set.univ)
    (fun x _ ↦ ψ.differentiableAt (x := x)) (fun x _ ↦ hderiv x)
    convex_univ (Set.mem_univ t) (Set.mem_univ s)
  simpa only [Real.norm_eq_abs] using hb

theorem scaled_fourier_difference_bounds (φ : 𝓢(ℝ, ℂ)) {C : ℝ}
    (hC : 0 < C) (hnorm : ∀ t : ℝ, ‖𝓕 φ t‖ ≤ C)
    (hdecay : ∀ t : ℝ, |t| * ‖𝓕 φ t‖ ≤ C)
    (hlip : ∀ s t : ℝ, ‖𝓕 φ s - 𝓕 φ t‖ ≤ C * |s - t|)
    {δ ρ : ℝ} (hδ : 0 < δ) (hδρ : δ ≤ ρ) (ξ : ℝ) :
    ‖𝓕 φ (δ * ξ) - 𝓕 φ (ρ * ξ)‖ ≤ C * ρ * |ξ| ∧
      ‖𝓕 φ (δ * ξ) - 𝓕 φ (ρ * ξ)‖ ≤ 2 * C * min 1 (1 / (δ * |ξ|)) := by
  have hρ : 0 < ρ := hδ.trans_le hδρ
  constructor
  · have hb := hlip (δ * ξ) (ρ * ξ)
    rw [← sub_mul, abs_mul, abs_of_nonpos (sub_nonpos.mpr hδρ)] at hb
    have hcoef : C * (-(δ - ρ)) * |ξ| ≤ C * ρ * |ξ| := by gcongr; linarith
    exact hb.trans (by nlinarith only [hcoef])
  · by_cases hξ : ξ = 0
    · subst ξ
      simp
    have hξp : 0 < |ξ| := abs_pos.mpr hξ
    have hd : ‖𝓕 φ (δ * ξ)‖ ≤ C / (δ * |ξ|) := by
      apply (le_div_iff₀ (mul_pos hδ hξp)).mpr
      have h := hdecay (δ * ξ)
      rw [abs_mul, abs_of_pos hδ] at h
      nlinarith
    have hr : ‖𝓕 φ (ρ * ξ)‖ ≤ C / (δ * |ξ|) := by
      have h := hdecay (ρ * ξ)
      rw [abs_mul, abs_of_pos hρ] at h
      apply (le_div_iff₀ (mul_pos hδ hξp)).mpr
      have hm := mul_le_mul_of_nonneg_right hδρ
        (mul_nonneg hξp.le (norm_nonneg (𝓕 φ (ρ * ξ))))
      nlinarith
    have hplain := (norm_sub_le _ _).trans (add_le_add (hnorm (δ * ξ)) (hnorm (ρ * ξ)))
    have hhigh := (norm_sub_le _ _).trans (add_le_add hd hr)
    rw [mul_min_of_nonneg _ _ (by positivity : 0 ≤ 2 * C)]
    apply le_min
    · nlinarith
    · convert hhigh using 1
      ring

end Erdos421
