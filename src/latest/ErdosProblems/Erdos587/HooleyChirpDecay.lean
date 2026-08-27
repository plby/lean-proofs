import ErdosProblems.Erdos587.ReciprocalPoisson

/-!
# A stationary-phase envelope for positive quadratic chirps

The existing exact Fresnel identity and uniform profile estimates give
the square-root decay and expanding Fourier scale simultaneously. The
bounded-parameter range follows from uniform Schwartz seminorm bounds.
-/

open scoped FourierTransform SchwartzMap

namespace Erdos587

lemma delta_weighted_norm_le_of_two_bounds {x u C₀ C₂ : ℝ} (hu : 0 ≤ u)
    (h₀ : u ≤ C₀) (h₂ : x ^ 2 * u ≤ C₂) :
    (1 + x) ^ 2 * u ≤ 2 * (C₀ + C₂) := by
  have hsquare : (1 + x) ^ 2 ≤ 2 * (1 + x ^ 2) := by nlinarith [sq_nonneg (x - 1)]
  nlinarith [mul_le_mul_of_nonneg_right hsquare hu]

theorem exists_delta_small_chirp_fourier_decay (f : 𝓢(ℝ, ℂ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ A : ℝ, |A| ≤ 1 → ∀ ξ : ℝ,
      (1 + |ξ|) ^ 2 * ‖𝓕 (quadraticChirpMul A f) ξ‖ ≤ C := by
  let T : 𝓢(ℝ, ℂ) →L[ℝ] 𝓢(ℝ, ℂ) := FourierTransform.fourierCLM ℝ 𝓢(ℝ, ℂ)
  obtain ⟨C₀, hC₀, h₀⟩ := exists_uniform_linear_quadraticChirpMul_seminorm_bound f T 0 0
  obtain ⟨C₂, hC₂, h₂⟩ := exists_uniform_linear_quadraticChirpMul_seminorm_bound f T 2 0
  refine ⟨2 * (C₀ + C₂), by positivity, ?_⟩
  intro A hA ξ
  have hb₀ := (SchwartzMap.le_seminorm' ℝ 0 0 (T (quadraticChirpMul A f)) ξ).trans (h₀ A hA)
  have hb₂ := (SchwartzMap.le_seminorm' ℝ 2 0 (T (quadraticChirpMul A f)) ξ).trans (h₂ A hA)
  simp only [pow_zero, one_mul, iteratedDeriv_zero] at hb₀
  simp only [iteratedDeriv_zero] at hb₂
  exact delta_weighted_norm_le_of_two_bounds (norm_nonneg _) hb₀ hb₂

theorem exists_delta_positive_chirp_fourier_envelope (f : 𝓢(ℝ, ℂ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ A : ℝ, 0 ≤ A → ∀ ξ : ℝ,
      Real.sqrt (1 + A) * (1 + |ξ| / (1 + A)) ^ 2 *
        ‖𝓕 (quadraticChirpMul A f) ξ‖ ≤ C := by
  obtain ⟨C₀, hC₀, hsmall⟩ := exists_delta_small_chirp_fourier_decay f
  obtain ⟨C₁, hC₁, hlarge⟩ := exists_uniform_fresnelProfile_derivative_bound f 2 0
  refine ⟨2 * C₀ + 4 * C₁ + 1, by positivity, ?_⟩
  intro A hA ξ
  have hH : 0 < 1 + A := by linarith
  by_cases hA1 : A ≤ 1
  · have hroot : Real.sqrt (1 + A) ≤ 2 := by
      apply (Real.sqrt_le_iff).mpr
      exact ⟨by norm_num, by nlinarith⟩
    have hratio : |ξ| / (1 + A) ≤ |ξ| := div_le_self (abs_nonneg ξ) (by linarith)
    have hweight : (1 + |ξ| / (1 + A)) ^ 2 ≤ (1 + |ξ|) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (by linarith) 2
    have hbound := hsmall A (abs_le.mpr ⟨by linarith, hA1⟩) ξ
    calc
      _ ≤ 2 * (1 + |ξ|) ^ 2 * ‖𝓕 (quadraticChirpMul A f) ξ‖ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul hroot hweight (by positivity) (by norm_num)) (norm_nonneg _)
      _ ≤ 2 * C₀ := by nlinarith
      _ ≤ _ := by linarith
  · have hApos : 0 < A := by linarith
    have hAsq : 0 < Real.sqrt (2 * A) := Real.sqrt_pos.mpr (by positivity)
    have hroot : Real.sqrt (1 + A) ≤ Real.sqrt (2 * A) :=
      Real.sqrt_le_sqrt (by linarith)
    have hroots : Real.sqrt (1 + A) / Real.sqrt (2 * A) ≤ 1 :=
      (div_le_one hAsq).mpr hroot
    have hscale : |ξ| / (1 + A) ≤ 2 * |ξ / (2 * A)| := by
      rw [abs_div, abs_of_pos (by positivity : 0 < 2 * A)]
      have hdiv : |ξ| / (1 + A) ≤ |ξ| / A :=
        div_le_div_of_nonneg_left (abs_nonneg ξ) hApos (by linarith)
      calc
        _ ≤ |ξ| / A := hdiv
        _ = _ := by field_simp
    have hweight : (1 + |ξ| / (1 + A)) ^ 2 ≤ 4 * (1 + |ξ / (2 * A)|) ^ 2 := by
      have hlinear : 1 + |ξ| / (1 + A) ≤ 2 * (1 + |ξ / (2 * A)|) := by linarith
      have h := pow_le_pow_left₀ (by positivity) hlinear 2
      nlinarith
    have hbound := hlarge A (le_of_not_ge hA1) (ξ / (2 * A))
    simp only [iteratedDeriv_zero] at hbound
    rw [fourier_quadraticChirpMul f hApos ξ, norm_mul, norm_mul, norm_phase, mul_one,
      norm_fresnelPrefactor hApos]
    calc
      _ = (Real.sqrt (1 + A) / Real.sqrt (2 * A)) *
          ((1 + |ξ| / (1 + A)) ^ 2 * ‖fresnelProfile f A (ξ / (2 * A))‖) := by ring
      _ ≤ 1 * (4 * (1 + |ξ / (2 * A)|) ^ 2 * ‖fresnelProfile f A (ξ / (2 * A))‖) :=
        mul_le_mul hroots (mul_le_mul_of_nonneg_right hweight (norm_nonneg _))
          (by positivity) (by norm_num)
      _ ≤ 4 * C₁ := by nlinarith
      _ ≤ _ := by linarith

end Erdos587
