import ErdosProblems.Erdos421.SchwartzWindowBounds
import ErdosProblems.Erdos421.SchwartzMellinEnergy

/-! # The Fourier multiplier for two normalized logarithmic windows -/

namespace Erdos421

open Complex MeasureTheory FourierTransform
open scoped SchwartzMap

noncomputable def windowMultiplier (φ : 𝓢(ℝ, ℂ)) (δ ρ t : ℝ) : ℂ :=
  𝓕 φ (δ * (t / (2 * Real.pi))) - 𝓕 φ (ρ * (t / (2 * Real.pi)))

theorem windowMultiplier_continuous (φ : 𝓢(ℝ, ℂ)) (δ ρ : ℝ) :
    Continuous (windowMultiplier φ δ ρ) :=
  ((𝓕 φ).continuous.comp (continuous_const.mul (continuous_id.div_const _))).sub
    ((𝓕 φ).continuous.comp (continuous_const.mul (continuous_id.div_const _)))

theorem normalized_window_mellin_energy (S : Finset ℕ) (a : ℕ → ℂ)
    (hS : ∀ n ∈ S, 0 < n) (σ : ℝ) (φ : 𝓢(ℝ, ℂ))
    {δ ρ : ℝ} (hδ : 0 < δ) (hρ : 0 < ρ) :
    (∫ y : ℝ, ‖schwartzDirichletWindow S a σ (normalizedSchwartzScale δ hδ φ) y -
      schwartzDirichletWindow S a σ (normalizedSchwartzScale ρ hρ φ) y‖ ^ 2) =
      (1 / (2 * Real.pi)) * ∫ t : ℝ,
        ‖dirichletPolynomial S a (σ + t * I)‖ ^ 2 * ‖windowMultiplier φ δ ρ t‖ ^ 2 := by
  rw [schwartzDirichletWindow_difference_mellin_energy S a hS]
  simp only [fourier_normalizedSchwartzScale, windowMultiplier]

theorem exists_schwartz_fourier_decay (φ : 𝓢(ℝ, ℂ)) (k : ℕ) :
    ∃ C > 0, ∀ t : ℝ, |t| ^ k * ‖𝓕 φ t‖ ≤ C := by
  let p : ℝ := SchwartzMap.seminorm ℝ k 0 (𝓕 φ)
  have hp : 0 ≤ p := apply_nonneg _ _
  refine ⟨p + 1, by positivity, ?_⟩
  intro t
  have h := SchwartzMap.le_seminorm' ℝ k 0 (𝓕 φ) t
  simp only [iteratedDeriv_zero] at h
  exact h.trans (by dsimp only [p]; linarith)

theorem windowMultiplier_bounds (φ : 𝓢(ℝ, ℂ)) {C : ℝ}
    (hC : 0 < C) (hnorm : ∀ t : ℝ, ‖𝓕 φ t‖ ≤ C)
    (hdecay : ∀ t : ℝ, |t| * ‖𝓕 φ t‖ ≤ C)
    (hlip : ∀ s t : ℝ, ‖𝓕 φ s - 𝓕 φ t‖ ≤ C * |s - t|)
    {δ ρ : ℝ} (hδ : 0 < δ) (hδρ : δ ≤ ρ) (t : ℝ) :
    ‖windowMultiplier φ δ ρ t‖ ≤ C * ρ * |t| / (2 * Real.pi) ∧
      ‖windowMultiplier φ δ ρ t‖ ≤
        2 * C * min 1 ((2 * Real.pi) / (δ * |t|)) := by
  have hpi : 0 < 2 * Real.pi := by positivity
  have hb := scaled_fourier_difference_bounds φ hC hnorm hdecay hlip hδ hδρ
    (t / (2 * Real.pi))
  rw [abs_div, abs_of_pos hpi] at hb
  have he : 1 / (δ * (|t| / (2 * Real.pi))) = (2 * Real.pi) / (δ * |t|) := by
    field_simp
  change ‖windowMultiplier φ δ ρ t‖ ≤ C * ρ * (|t| / (2 * Real.pi)) ∧
    ‖windowMultiplier φ δ ρ t‖ ≤ 2 * C * min 1 (1 / (δ * (|t| / (2 * Real.pi)))) at hb
  rw [he] at hb
  exact ⟨by simpa only [mul_div_assoc] using hb.1, hb.2⟩

theorem windowMultiplier_inverse_scale_bound (φ : 𝓢(ℝ, ℂ)) {C : ℝ}
    (hC : 0 < C) (hnorm : ∀ t : ℝ, ‖𝓕 φ t‖ ≤ C)
    (hdecay : ∀ t : ℝ, |t| * ‖𝓕 φ t‖ ≤ C)
    (hlip : ∀ s t : ℝ, ‖𝓕 φ s - 𝓕 φ t‖ ≤ C * |s - t|)
    {R ρ t : ℝ} (hR : 0 < R) (hρ : 4 * Real.pi / R ≤ ρ) (ht : 0 < t) :
    ‖windowMultiplier φ (4 * Real.pi / R) ρ t‖ ^ 2 ≤
      (4 * C ^ 2) * (min 1 ((R / 2) / t)) ^ 2 := by
  have hδ : 0 < 4 * Real.pi / R := by positivity
  have hb := (windowMultiplier_bounds φ hC hnorm hdecay hlip hδ hρ t).2
  rw [abs_of_pos ht] at hb
  have he : (2 * Real.pi) / (4 * Real.pi / R * t) = (R / 2) / t := by
    have hpi := Real.pi_ne_zero
    field_simp
    ring
  rw [he] at hb
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hb 2
  nlinarith only [hsq]

end Erdos421
