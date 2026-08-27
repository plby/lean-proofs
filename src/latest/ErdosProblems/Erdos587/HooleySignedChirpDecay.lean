import ErdosProblems.Erdos587.HooleyChirpDecay
import ErdosProblems.Erdos587.SignedNearby

/-! # The stationary-phase envelope for either sign of the chirp -/

open MeasureTheory
open scoped FourierTransform SchwartzMap ComplexConjugate

namespace Erdos587

lemma delta_fourier_conjugateSchwartz (f : 𝓢(ℝ, ℂ)) (ξ : ℝ) :
    𝓕 (conjugateSchwartz f) ξ = conj (𝓕 f (-ξ)) := by
  simp only [SchwartzMap.fourier_coe, fourier_eq_phase_integral]
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [map_mul, ← phase_neg, conjugateSchwartz_apply]
  congr 1
  congr 1
  ring

lemma delta_conjugate_quadraticChirpMul (f : 𝓢(ℝ, ℂ)) (A : ℝ) :
    conjugateSchwartz (quadraticChirpMul A f) = quadraticChirpMul (-A) (conjugateSchwartz f) := by
  ext x
  simp only [conjugateSchwartz_apply, quadraticChirpMul_apply, map_mul, ← phase_neg, neg_mul]

theorem exists_delta_chirp_fourier_envelope (f : 𝓢(ℝ, ℂ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ A ξ : ℝ,
      Real.sqrt (1 + |A|) * (1 + |ξ| / (1 + |A|)) ^ 2 *
        ‖𝓕 (quadraticChirpMul A f) ξ‖ ≤ C := by
  obtain ⟨C₀, hC₀, hpos⟩ := exists_delta_positive_chirp_fourier_envelope f
  obtain ⟨C₁, hC₁, hneg⟩ := exists_delta_positive_chirp_fourier_envelope (conjugateSchwartz f)
  refine ⟨C₀ + C₁, by positivity, ?_⟩
  intro A ξ
  by_cases hA : 0 ≤ A
  · rw [abs_of_nonneg hA]
    exact (hpos A hA ξ).trans (le_add_of_nonneg_right hC₁.le)
  · have hminus : 0 ≤ -A := by linarith
    have h := hneg (-A) hminus (-ξ)
    rw [← delta_conjugate_quadraticChirpMul, delta_fourier_conjugateSchwartz,
      neg_neg, Complex.norm_conj, abs_neg] at h
    rw [abs_of_neg (lt_of_not_ge hA)]
    exact h.trans (le_add_of_nonneg_left hC₀.le)

theorem exists_delta_chirp_fourier_decay (f : 𝓢(ℝ, ℂ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ A ξ : ℝ,
      ‖𝓕 (quadraticChirpMul A f) ξ‖ ≤
        C / Real.sqrt (1 + |A|) / (1 + |ξ| / (1 + |A|)) ^ 2 := by
  obtain ⟨C, hC, hbound⟩ := exists_delta_chirp_fourier_envelope f
  refine ⟨C, hC, ?_⟩
  intro A ξ
  have hroot : 0 < Real.sqrt (1 + |A|) := Real.sqrt_pos.mpr (by positivity)
  have hweight : 0 < (1 + |ξ| / (1 + |A|)) ^ 2 := by positivity
  apply (le_div_iff₀ hweight).mpr
  apply (le_div_iff₀ hroot).mpr
  calc
    _ = Real.sqrt (1 + |A|) * (1 + |ξ| / (1 + |A|)) ^ 2 *
        ‖𝓕 (quadraticChirpMul A f) ξ‖ := by ring
    _ ≤ C := hbound A ξ

end Erdos587
