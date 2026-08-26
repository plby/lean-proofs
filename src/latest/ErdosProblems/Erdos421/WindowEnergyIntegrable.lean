import ErdosProblems.Erdos421.SchwartzWindowMultiplier

/-! # Integrability and frequency decomposition of smooth-window energies -/

namespace Erdos421

open Complex MeasureTheory FourierTransform Set
open scoped SchwartzMap

theorem windowMultiplier_square_integrable (φ : 𝓢(ℝ, ℂ)) {δ ρ : ℝ}
    (hδ : 0 < δ) (hρ : 0 < ρ) : Integrable (fun t : ℝ ↦ ‖windowMultiplier φ δ ρ t‖ ^ 2) := by
  let ψ : 𝓢(ℝ, ℂ) := 𝓕 (normalizedSchwartzScale δ hδ φ - normalizedSchwartzScale ρ hρ φ)
  have hsub : 𝓕 (normalizedSchwartzScale δ hδ φ - normalizedSchwartzScale ρ hρ φ) =
      𝓕 (normalizedSchwartzScale δ hδ φ) - 𝓕 (normalizedSchwartzScale ρ hρ φ) :=
    (fourierCLM ℂ 𝓢(ℝ, ℂ)).map_sub _ _
  have hpi : 2 * Real.pi ≠ 0 := (by positivity : 0 < 2 * Real.pi).ne'
  have hi := (ψ.memLp 2).integrable_norm_pow (by decide : 2 ≠ 0)
  have hc := hi.comp_mul_left' (inv_ne_zero hpi)
  have he : ∀ t : ℝ, ψ ((2 * Real.pi)⁻¹ * t) = windowMultiplier φ δ ρ t := by
    intro t
    dsimp only [ψ]
    rw [hsub]
    simp only [sub_apply, fourier_normalizedSchwartzScale, windowMultiplier, div_eq_mul_inv,
      mul_comm t ((2 * Real.pi)⁻¹)]
  simpa only [he] using hc

theorem bounded_window_energy_integrable (φ : 𝓢(ℝ, ℂ)) {δ ρ B : ℝ}
    (hδ : 0 < δ) (hρ : 0 < ρ) {D : ℝ → ℂ} (hD : Continuous D)
    (hbound : ∀ t : ℝ, ‖D t‖ ≤ B) :
    Integrable (fun t : ℝ ↦ ‖D t‖ ^ 2 * ‖windowMultiplier φ δ ρ t‖ ^ 2) := by
  apply (windowMultiplier_square_integrable φ hδ hρ).bdd_mul (c := B ^ 2)
    (hD.norm.pow 2).aestronglyMeasurable
  filter_upwards [] with t
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (norm_nonneg _) (hbound t) 2

theorem integral_eq_five_frequency_bands {f : ℝ → ℝ} (hf : Integrable f) (U V : ℝ) :
    (∫ t : ℝ, f t) = (∫ t : ℝ in Iic (-V), f t) + (∫ t in -V..-U, f t) +
      (∫ t in -U..U, f t) + (∫ t in U..V, f t) + (∫ t : ℝ in Ioi V, f t) := by
  have hpart := intervalIntegral.integral_Iic_add_Ioi (b := V) hf.integrableOn hf.integrableOn
  have hmid := intervalIntegral.integral_Iic_sub_Iic (a := -V) (b := V)
    hf.integrableOn hf.integrableOn
  have h₁ := intervalIntegral.integral_add_adjacent_intervals
    (a := -V) (b := -U) (c := U) hf.intervalIntegrable hf.intervalIntegrable
  have h₂ := intervalIntegral.integral_add_adjacent_intervals
    (a := -V) (b := U) (c := V) hf.intervalIntegrable hf.intervalIntegrable
  linarith

end Erdos421
