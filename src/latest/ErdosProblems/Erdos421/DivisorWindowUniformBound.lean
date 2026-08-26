import ErdosProblems.Erdos421.DivisorWindowMeanSquare
import ErdosProblems.Erdos421.SchwartzWindowMultiplier

/-! # Unconditional uniform type-I window bound -/

namespace Erdos421

open MeasureTheory FourierTransform
open scoped SchwartzMap

theorem exists_divisor_window_fourier_bounds (φ : 𝓢(ℝ, ℂ)) :
    ∃ C : ℝ, 0 < C ∧ (∀ t : ℝ, ‖𝓕 φ t‖ ≤ C / (1 + |t|)) ∧
      (∀ t : ℝ, |t| ^ 2 * ‖𝓕 φ t‖ ≤ C) := by
  obtain ⟨C₁, hC₁, hφ₁⟩ := exists_schwartz_fourier_reciprocal_bound φ
  obtain ⟨C₂, hC₂, hφ₂⟩ := exists_schwartz_fourier_decay φ 2
  refine ⟨C₁ + C₂, add_pos hC₁ hC₂, ?_, ?_⟩
  · intro t
    exact (hφ₁ t).trans (div_le_div_of_nonneg_right (by linarith) (by positivity))
  · intro t
    exact (hφ₂ t).trans (by linarith)

/-- Every fixed Schwartz test function has one constant controlling all
bounded-coefficient divisibility windows and every finite truncation height. -/
theorem exists_weighted_divisor_window_mean_square_bound (φ : 𝓢(ℝ, ℂ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset ℕ) (a : ℕ → ℂ) (M H : ℕ),
      0 < M → 0 < H → (∀ m ∈ S, 0 < m ∧ m ≤ M) → (∀ m ∈ S, ‖a m‖ ≤ 1) →
      ∀ (Y u v : ℝ), 0 < Y → u ≤ v →
      (∫ x in u..v, ‖∑ m ∈ S, a m * (additiveDivisorWindow φ Y x m -
        (m : ℂ)⁻¹ * (∫ z : ℝ, φ z))‖ ^ 2) ≤
        2 * ((v - u + 16 * M ^ 2 * Real.log (4 * Real.pi * H * M ^ 2 + 2)) *
          (2 * C ^ 2 * (harmonic M : ℝ) ^ 3 / Y)) +
        2 * (v - u) * (2 * C * M ^ 2 / (Y ^ 2 * H)) ^ 2 := by
  obtain ⟨C, hC, hφ₁, hφ₂⟩ := exists_divisor_window_fourier_bounds φ
  refine ⟨C, hC, ?_⟩
  intro S a M H hM hH hS ha Y u v hY huv
  exact weighted_divisor_window_mean_square φ hC.le hφ₁ hφ₂ S a hM hH hS ha hY huv

end Erdos421
