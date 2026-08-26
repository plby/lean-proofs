import ErdosProblems.Erdos421.DivisorWindowSpectrum
import ErdosProblems.Erdos421.RationalFrequencyMean

/-! # The finite-spectrum type-I mean-square estimate -/

namespace Erdos421

open MeasureTheory FourierTransform
open scoped SchwartzMap

theorem divisor_spectrum_mean_square (φ : 𝓢(ℝ, ℂ)) {C : ℝ}
    (hφ : ∀ t : ℝ, ‖𝓕 φ t‖ ≤ C / (1 + |t|))
    (S : Finset ℕ) (a : ℕ → ℂ) {M : ℕ} (hM : 0 < M)
    (hS : ∀ m ∈ S, 0 < m ∧ m ≤ M) (ha : ∀ m ∈ S, ‖a m‖ ≤ 1)
    (F : Finset ℚ) (hFden : ∀ q ∈ F, q.den ≤ M) (hFzero : ∀ q ∈ F, q ≠ 0)
    {R Y : ℝ} (hR : 0 ≤ R) (hY : 0 < Y) (hspan : ∀ q ∈ F, |(q : ℝ)| ≤ R)
    {u v : ℝ} (huv : u ≤ v) :
    (∫ x in u..v, ‖∑ q ∈ F, (divisorFourierCoefficient S a q * 𝓕 φ (Y * q)) *
        oscillatoryPhase (2 * Real.pi * q) x‖ ^ 2) ≤
      (v - u + 16 * M ^ 2 * Real.log (4 * Real.pi * R * M ^ 2 + 2)) *
        (2 * C ^ 2 * (harmonic M : ℝ) ^ 3 / Y) := by
  have hlog : 0 ≤ Real.log (4 * Real.pi * R * (M : ℝ) ^ 2 + 2) := by
    apply Real.log_nonneg
    have hh : 0 ≤ 4 * Real.pi * R * (M : ℝ) ^ 2 := by positivity
    linarith
  have hfactor : 0 ≤ v - u + 16 * (M : ℝ) ^ 2 *
      Real.log (4 * Real.pi * R * (M : ℝ) ^ 2 + 2) := by positivity
  exact (rational_frequency_mean_square_bound F
    (fun q ↦ divisorFourierCoefficient S a q * 𝓕 φ (Y * q)) hM hFden hspan u v).trans
      (mul_le_mul_of_nonneg_left
        (divisor_window_spectrum_energy φ hφ S a hS ha F hFden hFzero hY) hfactor)

end Erdos421
