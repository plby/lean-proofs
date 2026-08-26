import ErdosProblems.Erdos421.WindowLowFrequency
import ErdosProblems.Erdos421.WindowFrequencyTails
import ErdosProblems.Erdos421.WindowEnergyIntegrable

/-! # Assembling the five frequency contributions to a window variance -/

namespace Erdos421

open Complex MeasureTheory FourierTransform Set
open scoped SchwartzMap

theorem window_energy_le_of_middle_bounds (φ : 𝓢(ℝ, ℂ)) {C K : ℝ}
    (hC : 0 < C) (hnorm : ∀ t : ℝ, ‖𝓕 φ t‖ ≤ C)
    (hdecay : ∀ t : ℝ, |t| * ‖𝓕 φ t‖ ≤ C)
    (hlip : ∀ s t : ℝ, ‖𝓕 φ s - 𝓕 φ t‖ ≤ C * |s - t|)
    (hK : 0 ≤ K) (k : ℕ) (hrapid : ∀ t : ℝ, |t| ^ (k + 1) * ‖𝓕 φ t‖ ≤ K)
    {R ρ U V Q : ℝ} (hR : 0 < R) (hρ : 4 * Real.pi / R ≤ ρ)
    (hU : 0 ≤ U) (hV : 0 < V) {D : ℝ → ℂ} (hD : Continuous D)
    (hDbound : ∀ t : ℝ, ‖D t‖ ≤ 1)
    (hpositive : (∫ t in U..V, ‖D t‖ ^ 2 *
      ‖windowMultiplier φ (4 * Real.pi / R) ρ t‖ ^ 2) ≤ Q)
    (hnegative : (∫ t in -V..-U, ‖D t‖ ^ 2 *
      ‖windowMultiplier φ (4 * Real.pi / R) ρ t‖ ^ 2) ≤ Q) :
    (∫ t : ℝ, ‖D t‖ ^ 2 * ‖windowMultiplier φ (4 * Real.pi / R) ρ t‖ ^ 2) ≤
      2 * Q + 2 * (C * ρ / (2 * Real.pi)) ^ 2 * U ^ 3 +
        2 * ((2 * K * (R / 2) ^ (k + 1)) ^ 2 / (V ^ k) ^ 2 / V) := by
  have hδ : 0 < 4 * Real.pi / R := by positivity
  have hρp : 0 < ρ := hδ.trans_le hρ
  have hF := bounded_window_energy_integrable φ hδ hρp hD hDbound
  have hlow := windowMultiplier_low_frequency_bound φ hC hnorm hdecay hlip hδ hρ hU hD hDbound
  have hleft := windowMultiplier_Iic_tail φ D k hK hrapid hR hρ hV hDbound
  have hright := windowMultiplier_Ioi_tail φ D k hK hrapid hR hρ hV hDbound
  rw [integral_eq_five_frequency_bands hF U V]
  linarith

end Erdos421
