import ErdosProblems.Erdos421.DivisorFourierCoefficients
import ErdosProblems.Erdos421.SchwartzWindowBounds
import ErdosProblems.Erdos421.RationalCoefficientEnergy

/-! # Square energy of the smoothed divisibility spectrum -/

namespace Erdos421

open FourierTransform
open scoped SchwartzMap

theorem exists_schwartz_fourier_reciprocal_bound (φ : 𝓢(ℝ, ℂ)) :
    ∃ C > 0, ∀ t : ℝ, ‖𝓕 φ t‖ ≤ C / (1 + |t|) := by
  obtain ⟨C, hC, hnorm, hdecay, _⟩ := exists_schwartz_fourier_bounds φ
  refine ⟨2 * C, by positivity, ?_⟩
  intro t
  apply (le_div_iff₀ (by positivity : 0 < 1 + |t|)).mpr
  nlinarith [hnorm t, hdecay t]

theorem rational_window_coefficient_bound (φ : 𝓢(ℝ, ℂ)) {C H Y : ℝ}
    (hφ : ∀ t : ℝ, ‖𝓕 φ t‖ ≤ C / (1 + |t|)) (hH : 0 ≤ H) (hY : 0 < Y)
    (q : ℚ) {c : ℂ} (hc : ‖c‖ ≤ H / q.den) :
    ‖c * 𝓕 φ (Y * q)‖ ≤ C * H / ((q.den : ℝ) + Y * |(q.num : ℝ)|) := by
  have hd : (0 : ℝ) < q.den := by exact_mod_cast q.den_pos
  rw [norm_mul]
  calc
    _ ≤ (H / q.den) * (C / (1 + |Y * (q : ℝ)|)) :=
      mul_le_mul hc (hφ (Y * q)) (norm_nonneg _) (div_nonneg hH hd.le)
    _ = _ := by
      rw [abs_mul, abs_of_pos hY, Rat.cast_def q, abs_div, abs_of_pos hd]
      field_simp

theorem divisor_window_coefficient_bound (φ : 𝓢(ℝ, ℂ)) {C : ℝ}
    (hφ : ∀ t : ℝ, ‖𝓕 φ t‖ ≤ C / (1 + |t|))
    (S : Finset ℕ) (a : ℕ → ℂ) {M : ℕ}
    (hS : ∀ m ∈ S, 0 < m ∧ m ≤ M) (ha : ∀ m ∈ S, ‖a m‖ ≤ 1)
    {Y : ℝ} (hY : 0 < Y) (q : ℚ) :
    ‖divisorFourierCoefficient S a q * 𝓕 φ (Y * q)‖ ≤
      C * (harmonic M : ℝ) / ((q.den : ℝ) + Y * |(q.num : ℝ)|) := by
  have hh : (0 : ℝ) ≤ harmonic M := by
    simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
    positivity
  exact rational_window_coefficient_bound φ hφ hh hY q
    (divisorFourierCoefficient_norm_le S a hS ha q)

theorem divisor_window_spectrum_energy (φ : 𝓢(ℝ, ℂ)) {C : ℝ}
    (hφ : ∀ t : ℝ, ‖𝓕 φ t‖ ≤ C / (1 + |t|))
    (S : Finset ℕ) (a : ℕ → ℂ) {M : ℕ}
    (hS : ∀ m ∈ S, 0 < m ∧ m ≤ M) (ha : ∀ m ∈ S, ‖a m‖ ≤ 1)
    (F : Finset ℚ) (hFden : ∀ q ∈ F, q.den ≤ M) (hFzero : ∀ q ∈ F, q ≠ 0)
    {Y : ℝ} (hY : 0 < Y) :
    (∑ q ∈ F, ‖divisorFourierCoefficient S a q * 𝓕 φ (Y * q)‖ ^ 2) ≤
      2 * C ^ 2 * (harmonic M : ℝ) ^ 3 / Y := by
  have hb := rational_coefficient_square_energy F
    (fun q ↦ divisorFourierCoefficient S a q * 𝓕 φ (Y * q)) hFden hFzero hY
    (fun q _ ↦ divisor_window_coefficient_bound φ hφ S a hS ha hY q)
  exact hb.trans_eq (by ring)

end Erdos421
