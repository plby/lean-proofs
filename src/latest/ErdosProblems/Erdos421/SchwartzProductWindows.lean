import ErdosProblems.Erdos421.SchwartzWindowMultiplier

/-! # Exact smooth-window energies for products of Dirichlet polynomials -/

namespace Erdos421

open Complex MeasureTheory FourierTransform
open scoped SchwartzMap

noncomputable def schwartzProductWindow (S T : Finset ℕ) (a b : ℕ → ℂ)
    (σ : ℝ) (φ : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ) :=
  schwartzDirichletWindow S a σ (schwartzDirichletWindow T b σ φ)

theorem fourier_schwartzProductWindow (S T : Finset ℕ) (a b : ℕ → ℂ)
    (hS : ∀ n ∈ S, 0 < n) (hT : ∀ n ∈ T, 0 < n) (σ : ℝ) (φ : 𝓢(ℝ, ℂ)) (ξ : ℝ) :
    𝓕 (schwartzProductWindow S T a b σ φ) ξ =
      (dirichletPolynomial S a (σ + (2 * Real.pi * ξ : ℝ) * I) *
        dirichletPolynomial T b (σ + (2 * Real.pi * ξ : ℝ) * I)) * 𝓕 φ ξ := by
  simp only [schwartzProductWindow, fourier_schwartzDirichletWindow S a hS,
    fourier_schwartzDirichletWindow T b hT, mul_assoc]

theorem schwartzProductWindow_difference_mellin_energy (S T : Finset ℕ) (a b : ℕ → ℂ)
    (hS : ∀ n ∈ S, 0 < n) (hT : ∀ n ∈ T, 0 < n) (σ : ℝ) (φ ψ : 𝓢(ℝ, ℂ)) :
    (∫ y : ℝ, ‖schwartzProductWindow S T a b σ φ y - schwartzProductWindow S T a b σ ψ y‖ ^ 2) =
      (1 / (2 * Real.pi)) * ∫ t : ℝ,
        ‖dirichletPolynomial S a (σ + t * I) * dirichletPolynomial T b (σ + t * I)‖ ^ 2 *
          ‖𝓕 φ (t / (2 * Real.pi)) - 𝓕 ψ (t / (2 * Real.pi))‖ ^ 2 := by
  have hpi : 2 * Real.pi ≠ 0 := (by positivity : 0 < 2 * Real.pi).ne'
  rw [schwartzProductWindow, schwartzProductWindow,
    schwartzDirichletWindow_difference_mellin_energy S a hS]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with t
  rw [fourier_schwartzDirichletWindow T b hT, fourier_schwartzDirichletWindow T b hT,
    mul_div_cancel₀ t hpi, ← mul_sub, norm_mul, norm_mul]
  ring

theorem normalized_product_window_mellin_energy (S T : Finset ℕ) (a b : ℕ → ℂ)
    (hS : ∀ n ∈ S, 0 < n) (hT : ∀ n ∈ T, 0 < n) (σ : ℝ) (φ : 𝓢(ℝ, ℂ))
    {δ ρ : ℝ} (hδ : 0 < δ) (hρ : 0 < ρ) :
    (∫ y : ℝ, ‖schwartzProductWindow S T a b σ (normalizedSchwartzScale δ hδ φ) y -
      schwartzProductWindow S T a b σ (normalizedSchwartzScale ρ hρ φ) y‖ ^ 2) =
      (1 / (2 * Real.pi)) * ∫ t : ℝ,
        ‖dirichletPolynomial S a (σ + t * I) * dirichletPolynomial T b (σ + t * I)‖ ^ 2 *
          ‖windowMultiplier φ δ ρ t‖ ^ 2 := by
  rw [schwartzProductWindow_difference_mellin_energy S T a b hS hT]
  simp only [fourier_normalizedSchwartzScale, windowMultiplier]

end Erdos421
