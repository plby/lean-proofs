import ErdosProblems.Erdos421.SchwartzDirichletWindows

/-! # Smooth-window Plancherel in the Dirichlet-series frequency variable -/

namespace Erdos421

open Complex MeasureTheory FourierTransform
open scoped SchwartzMap

theorem schwartzDirichletWindow_mellin_energy (S : Finset ℕ) (a : ℕ → ℂ)
    (hS : ∀ n ∈ S, 0 < n) (σ : ℝ) (φ : 𝓢(ℝ, ℂ)) :
    (∫ y : ℝ, ‖schwartzDirichletWindow S a σ φ y‖ ^ 2) =
      (1 / (2 * Real.pi)) * ∫ t : ℝ,
        ‖dirichletPolynomial S a (σ + t * I)‖ ^ 2 * ‖𝓕 φ (t / (2 * Real.pi))‖ ^ 2 := by
  have hpi : 0 < 2 * Real.pi := by positivity
  let G : ℝ → ℝ := fun t ↦
    ‖dirichletPolynomial S a (σ + t * I)‖ ^ 2 * ‖𝓕 φ (t / (2 * Real.pi))‖ ^ 2
  have he : ∀ ξ : ℝ, G ((2 * Real.pi) * ξ) =
      ‖dirichletPolynomial S a (σ + (2 * Real.pi * ξ : ℝ) * I)‖ ^ 2 * ‖𝓕 φ ξ‖ ^ 2 := by
    intro ξ
    dsimp only [G]
    rw [mul_div_cancel_left₀ ξ hpi.ne']
  rw [schwartzDirichletWindow_plancherel S a hS σ φ]
  simp_rw [← he]
  have h := Measure.integral_comp_mul_left G (2 * Real.pi)
  simpa only [abs_of_pos (inv_pos.mpr hpi), smul_eq_mul, one_div] using h

theorem schwartzDirichletWindow_difference_mellin_energy (S : Finset ℕ) (a : ℕ → ℂ)
    (hS : ∀ n ∈ S, 0 < n) (σ : ℝ) (φ ψ : 𝓢(ℝ, ℂ)) :
    (∫ y : ℝ, ‖schwartzDirichletWindow S a σ φ y - schwartzDirichletWindow S a σ ψ y‖ ^ 2) =
      (1 / (2 * Real.pi)) * ∫ t : ℝ,
        ‖dirichletPolynomial S a (σ + t * I)‖ ^ 2 *
          ‖𝓕 φ (t / (2 * Real.pi)) - 𝓕 ψ (t / (2 * Real.pi))‖ ^ 2 := by
  have h := schwartzDirichletWindow_mellin_energy S a hS σ (φ - ψ)
  have hsub : 𝓕 (φ - ψ) = 𝓕 φ - 𝓕 ψ := (fourierCLM ℂ 𝓢(ℝ, ℂ)).map_sub φ ψ
  simpa only [schwartzDirichletWindow_sub, sub_apply, hsub] using h

end Erdos421
