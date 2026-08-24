import ErdosProblems.Erdos587.Periodization

/-!
# Integrating the periodized Fourier expansion

The summable absolute Fourier coefficients dominate each integrand by a
fixed integrable Schwartz weight. This justifies the integral/series swap.
-/

open MeasureTheory
open scoped BigOperators SchwartzMap FourierTransform

namespace Erdos587

lemma integrable_weighted_fourier_root (f : 𝓢(ℝ, ℂ)) {δ : ℝ} (hδ : 0 < δ)
    (a : ℂ) (m : ℤ) (θ : ℝ → ℝ) (hθ : Continuous θ) :
    Integrable (fun x : ℝ => a * phase ((m : ℝ) * θ x) * f (δ * x)) := by
  have hf : Integrable (fun x : ℝ => f (δ * x)) := by
    change Integrable (dilateSchwartz f δ hδ.ne' : ℝ → ℂ)
    exact (dilateSchwartz f δ hδ.ne').integrable
  have hphase : Continuous (fun x : ℝ => phase ((m : ℝ) * θ x)) := by
    unfold phase
    fun_prop
  have hcont : Continuous (fun x : ℝ => a * phase ((m : ℝ) * θ x) * f (δ * x)) :=
    (continuous_const.mul hphase).mul (f.continuous.comp (continuous_const.mul continuous_id))
  apply (hf.norm.const_mul ‖a‖).mono' hcont.aestronglyMeasurable
  filter_upwards [] with x
  simp only [norm_mul, norm_phase, mul_one, le_refl]

lemma integral_norm_weighted_fourier_root (f : 𝓢(ℝ, ℂ)) (δ : ℝ)
    (a : ℂ) (m : ℤ) (θ : ℝ → ℝ) :
    (∫ x : ℝ, ‖a * phase ((m : ℝ) * θ x) * f (δ * x)‖) =
      ‖a‖ * ∫ x : ℝ, ‖f (δ * x)‖ := by
  simp only [norm_mul, norm_phase, mul_one]
  exact integral_const_mul _ _

lemma summable_integral_norm_fourier_roots (f g : 𝓢(ℝ, ℂ)) (δ : ℝ) {σ : ℝ}
    (hσ : 0 < σ) (θ : ℝ → ℝ) :
    Summable (fun m : ℤ => ∫ x : ℝ,
      ‖scaledFourierCoeff g σ m * phase ((m : ℝ) * θ x) * f (δ * x)‖) := by
  simp only [integral_norm_weighted_fourier_root]
  exact (summable_scaledFourierCoeff g hσ).norm.mul_right _

lemma integral_periodization_eq_integral_series (f g : 𝓢(ℝ, ℂ)) (δ : ℝ) {σ : ℝ}
    (hσ : 0 < σ) (θ : ℝ → ℝ) :
    (∫ x : ℝ, f (δ * x) * periodizedSchwartz g σ (θ x)) =
      ∫ x : ℝ, ∑' m : ℤ, scaledFourierCoeff g σ m * phase ((m : ℝ) * θ x) * f (δ * x) := by
  apply integral_congr_ae
  filter_upwards [] with x
  rw [periodizedSchwartz_eq_fourier g hσ, ← tsum_mul_left]
  apply tsum_congr
  intro m
  exact mul_comm _ _

theorem integral_periodization_fourier_identity (f g : 𝓢(ℝ, ℂ)) {δ σ : ℝ}
    (hδ : 0 < δ) (hσ : 0 < σ) (θ : ℝ → ℝ) (hθ : Continuous θ) :
    (∫ x : ℝ, f (δ * x) * periodizedSchwartz g σ (θ x)) =
      ∑' m : ℤ, scaledFourierCoeff g σ m *
        ∫ x : ℝ, phase ((m : ℝ) * θ x) * f (δ * x) := by
  rw [integral_periodization_eq_integral_series f g δ hσ θ]
  calc
    _ = ∑' m : ℤ, ∫ x : ℝ,
        scaledFourierCoeff g σ m * phase ((m : ℝ) * θ x) * f (δ * x) :=
      (integral_tsum_of_summable_integral_norm
        (fun m => integrable_weighted_fourier_root f hδ (scaledFourierCoeff g σ m) m θ hθ)
        (summable_integral_norm_fourier_roots f g δ hσ θ)).symm
    _ = _ := by
      apply tsum_congr
      intro m
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with x
      exact mul_assoc _ _ _

lemma summable_integral_periodization_fourier (f g : 𝓢(ℝ, ℂ)) {δ σ : ℝ}
    (hδ : 0 < δ) (hσ : 0 < σ) (θ : ℝ → ℝ) (hθ : Continuous θ) :
    Summable (fun m : ℤ => scaledFourierCoeff g σ m *
      ∫ x : ℝ, phase ((m : ℝ) * θ x) * f (δ * x)) := by
  have hh := (hasSum_integral_of_summable_integral_norm
    (fun m => integrable_weighted_fourier_root f hδ (scaledFourierCoeff g σ m) m θ hθ)
    (summable_integral_norm_fourier_roots f g δ hσ θ)).summable
  apply hh.congr
  intro m
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  exact mul_assoc _ _ _

end Erdos587
