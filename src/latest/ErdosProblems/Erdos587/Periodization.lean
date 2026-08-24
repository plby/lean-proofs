import ErdosProblems.Erdos587.UniformNearby

/-!
# Periodized weights and their absolutely convergent Fourier expansions

The physical weight is fixed and dilated by its actual scale. Absolute
convergence justifies exchanging the root and Fourier sums.
-/

open scoped BigOperators SchwartzMap FourierTransform

namespace Erdos587

noncomputable def periodizedSchwartz (g : 𝓢(ℝ, ℂ)) (σ t : ℝ) : ℂ :=
  ∑' k : ℤ, g (σ⁻¹ * (t + k))

noncomputable def scaledFourierCoeff (g : 𝓢(ℝ, ℂ)) (σ : ℝ) (m : ℤ) : ℂ :=
  (σ : ℂ) * (𝓕 g : 𝓢(ℝ, ℂ)) (σ * m)

lemma summable_scaledFourierCoeff (g : 𝓢(ℝ, ℂ)) {σ : ℝ} (hσ : 0 < σ) :
    Summable (scaledFourierCoeff g σ) := by
  change Summable (fun m : ℤ => (σ : ℂ) * (𝓕 g : 𝓢(ℝ, ℂ)) (σ * m))
  simpa only [dilateSchwartz_apply] using
    (summable_schwartz_int (dilateSchwartz (𝓕 g) σ hσ.ne')).mul_left (σ : ℂ)

lemma periodizedSchwartz_eq_fourier (g : 𝓢(ℝ, ℂ)) {σ : ℝ} (hσ : 0 < σ) (t : ℝ) :
    periodizedSchwartz g σ t =
      ∑' m : ℤ, scaledFourierCoeff g σ m * phase ((m : ℝ) * t) := by
  have hh := poisson_arithmetic_progression g (inv_pos.mpr hσ) (σ⁻¹ * t)
  have harg (k : ℤ) : σ⁻¹ * t + σ⁻¹ * k = σ⁻¹ * (t + k) := by ring
  have hfreq (m : ℤ) : (m : ℝ) / σ⁻¹ = σ * m := by field_simp
  have hphase (m : ℤ) : (m : ℝ) * (σ⁻¹ * t) / σ⁻¹ = m * t := by field_simp
  simp_rw [harg, hfreq, hphase] at hh
  simp only [Complex.ofReal_inv, inv_inv] at hh
  change periodizedSchwartz g σ t = _ at hh
  rw [hh, ← tsum_mul_left]
  apply tsum_congr
  intro m
  unfold scaledFourierCoeff
  ring

lemma summable_norm_tensor {α β : Type*} {a : α → ℂ} {b : β → ℂ}
    (ha : Summable a) (hb : Summable b) :
    Summable (fun p : α × β => ‖a p.1‖ * ‖b p.2‖) := by
  apply (summable_prod_of_nonneg
    (f := fun p : α × β => ‖a p.1‖ * ‖b p.2‖)
    (fun p => mul_nonneg (norm_nonneg (a p.1)) (norm_nonneg (b p.2)))).mpr
  refine ⟨fun x => hb.norm.mul_left (‖a x‖), ?_⟩
  simp_rw [tsum_mul_left]
  exact ha.norm.mul_right _

lemma summable_weighted_fourier_roots (f g : 𝓢(ℝ, ℂ)) {δ σ : ℝ}
    (hδ : 0 < δ) (hσ : 0 < σ) (θ : ℤ → ℝ) :
    Summable (fun p : ℤ × ℤ => scaledFourierCoeff g σ p.1 *
      phase ((p.1 : ℝ) * θ p.2) * f (δ * p.2)) := by
  have hf : Summable (fun z : ℤ => f (δ * z)) := by
    simpa only [dilateSchwartz_apply] using summable_schwartz_int (dilateSchwartz f δ hδ.ne')
  have hh := summable_norm_tensor (summable_scaledFourierCoeff g hσ) hf
  apply Summable.of_norm
  simpa only [norm_mul, norm_phase, mul_one] using hh

lemma weighted_periodization_eq_iterated_series (f g : 𝓢(ℝ, ℂ)) (δ : ℝ) {σ : ℝ}
    (hσ : 0 < σ) (θ : ℤ → ℝ) :
    (∑' z : ℤ, f (δ * z) * periodizedSchwartz g σ (θ z)) =
      ∑' z : ℤ, ∑' m : ℤ, scaledFourierCoeff g σ m * phase ((m : ℝ) * θ z) * f (δ * z) := by
  apply tsum_congr
  intro z
  rw [periodizedSchwartz_eq_fourier g hσ, ← tsum_mul_left]
  apply tsum_congr
  intro m
  exact mul_comm _ _

theorem weighted_periodization_fourier_identity (f g : 𝓢(ℝ, ℂ)) {δ σ : ℝ}
    (hδ : 0 < δ) (hσ : 0 < σ) (θ : ℤ → ℝ) :
    (∑' z : ℤ, f (δ * z) * periodizedSchwartz g σ (θ z)) =
      ∑' m : ℤ, scaledFourierCoeff g σ m *
        ∑' z : ℤ, phase ((m : ℝ) * θ z) * f (δ * z) := by
  have hsum := summable_weighted_fourier_roots f g hδ hσ θ
  rw [weighted_periodization_eq_iterated_series f g δ hσ θ]
  calc
    _ = ∑' m : ℤ, ∑' z : ℤ, scaledFourierCoeff g σ m *
        phase ((m : ℝ) * θ z) * f (δ * z) :=
      Summable.tsum_comm (f := fun m z : ℤ => scaledFourierCoeff g σ m *
        phase ((m : ℝ) * θ z) * f (δ * z)) hsum
    _ = _ := by
      apply tsum_congr
      intro m
      rw [← tsum_mul_left]
      apply tsum_congr
      intro z
      exact mul_assoc _ _ _

end Erdos587
