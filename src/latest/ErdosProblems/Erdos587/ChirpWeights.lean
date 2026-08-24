import ErdosProblems.Erdos587.SchwartzWeights

/-!
# Uniform low-frequency chirp weights

For bounded quadratic modulation, all spatial decay and derivative bounds
are uniform. These are the weights in the centered low-frequency estimate.
-/

open scoped BigOperators SchwartzMap

namespace Erdos587

lemma one_add_pow_weight_bound (k : ℕ) {x y M₀ Mₖ : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hM₀ : 0 ≤ M₀) (hMₖ : 0 ≤ Mₖ)
    (hzero : y ≤ M₀) (hpow : x ^ k * y ≤ Mₖ) :
    (1 + x) ^ k * y ≤ 2 ^ k * (M₀ + Mₖ) := by
  by_cases hxone : x ≤ 1
  · calc
      _ ≤ 2 ^ k * y := by gcongr; linarith
      _ ≤ 2 ^ k * M₀ := mul_le_mul_of_nonneg_left hzero (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hMₖ) (by positivity)
  · have hxone' : 1 ≤ x := (lt_of_not_ge hxone).le
    calc
      _ ≤ (2 * x) ^ k * y := by gcongr; linarith
      _ = 2 ^ k * (x ^ k * y) := by rw [mul_pow]; ring
      _ ≤ 2 ^ k * Mₖ := mul_le_mul_of_nonneg_left hpow (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hM₀) (by positivity)

theorem exists_uniform_linear_chirp_derivative_bound (f : 𝓢(ℝ, ℂ))
    (T : 𝓢(ℝ, ℂ) →L[ℝ] 𝓢(ℝ, ℂ)) (k n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℝ, |u| ≤ 1 → ∀ x : ℝ,
      (1 + |x|) ^ k * ‖iteratedDeriv n (T (quadraticChirpMul u f) : ℝ → ℂ) x‖ ≤ C := by
  obtain ⟨M₀, hM₀, hb₀⟩ := exists_uniform_linear_quadraticChirpMul_seminorm_bound f T 0 n
  obtain ⟨Mₖ, hMₖ, hbₖ⟩ := exists_uniform_linear_quadraticChirpMul_seminorm_bound f T k n
  refine ⟨2 ^ k * (M₀ + Mₖ), by positivity, ?_⟩
  intro u hu x
  apply one_add_pow_weight_bound k (abs_nonneg x) (norm_nonneg _) hM₀ hMₖ
  · have h := SchwartzMap.le_seminorm' ℝ 0 n (T (quadraticChirpMul u f)) x
    simp only [pow_zero, one_mul] at h
    exact h.trans (hb₀ u hu)
  · exact (SchwartzMap.le_seminorm' ℝ k n (T (quadraticChirpMul u f)) x).trans (hbₖ u hu)

theorem exists_uniform_chirp_derivative_bound (f : 𝓢(ℝ, ℂ)) (k n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℝ, |u| ≤ 1 → ∀ x : ℝ,
      (1 + |x|) ^ k * ‖iteratedDeriv n (quadraticChirpMul u f : ℝ → ℂ) x‖ ≤ C := by
  exact exists_uniform_linear_chirp_derivative_bound f (ContinuousLinearMap.id ℝ 𝓢(ℝ, ℂ)) k n

theorem exists_uniform_chirp_block_variation_bound (f : 𝓢(ℝ, ℂ)) (p : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (A t u δ : ℝ) (K : ℕ) (j : ℤ),
      |A| ≤ 1 → 1 / 2 ≤ t → |u| ≤ 1 → 0 ≤ δ → δ * K ≤ 2 →
      finiteVariationNorm (fun n => quadraticChirpMul A f (t * j + u + δ * n)) K ≤
        C / (1 + |(j : ℝ)|) ^ p := by
  obtain ⟨M₀, hM₀, hb₀⟩ := exists_uniform_chirp_derivative_bound f p 0
  obtain ⟨M₁, hM₁, hb₁⟩ := exists_uniform_chirp_derivative_bound f p 1
  refine ⟨8 ^ p * (M₀ + 2 * M₁), by positivity, ?_⟩
  intro A t u δ K j hA ht hu hδ hKδ
  apply sample_block_variation_le_of_decay _ p (SchwartzMap.differentiable _)
    M₀ M₁ hM₁ _ _ t u δ K j ht hu hδ hKδ
  · intro y
    simpa only [iteratedDeriv_zero] using hb₀ A hA y
  · intro y
    simpa only [iteratedDeriv_one] using hb₁ A hA y

end Erdos587
