import ErdosProblems.Erdos587.IntegralPeriodization

/-! Positivity and domination for the physical periodized weights. -/

open MeasureTheory
open scoped BigOperators SchwartzMap FourierTransform

namespace Erdos587

lemma summable_periodizedSchwartz (g : 𝓢(ℝ, ℂ)) {σ : ℝ} (hσ : 0 < σ) (t : ℝ) :
    Summable (fun k : ℤ => g (σ⁻¹ * (t + k))) := by
  have hh := summable_schwartz_int
    (dilateSchwartz (g.compSubConstCLM ℂ (-(σ⁻¹ * t))) σ⁻¹ (inv_ne_zero hσ.ne'))
  apply hh.congr
  intro k
  rw [dilateSchwartz_apply, SchwartzMap.compSubConstCLM_apply]
  congr 1
  ring

lemma norm_periodizedSchwartz_le (g : 𝓢(ℝ, ℂ)) {σ : ℝ} (hσ : 0 < σ) (t : ℝ) :
    ‖periodizedSchwartz g σ t‖ ≤ ∑' m : ℤ, ‖scaledFourierCoeff g σ m‖ := by
  have hs : Summable (fun m : ℤ => ‖scaledFourierCoeff g σ m * phase ((m : ℝ) * t)‖) := by
    simpa only [norm_mul, norm_phase, mul_one] using (summable_scaledFourierCoeff g hσ).norm
  rw [periodizedSchwartz_eq_fourier g hσ]
  apply (norm_tsum_le_tsum_norm hs).trans_eq
  apply tsum_congr
  intro m
  simp only [norm_mul, norm_phase, mul_one]

lemma continuous_periodizedSchwartz (g : 𝓢(ℝ, ℂ)) {σ : ℝ} (hσ : 0 < σ) :
    Continuous (periodizedSchwartz g σ) := by
  have heq : periodizedSchwartz g σ = fun t : ℝ =>
      ∑' m : ℤ, scaledFourierCoeff g σ m * phase ((m : ℝ) * t) := by
    funext t
    exact periodizedSchwartz_eq_fourier g hσ t
  rw [heq]
  have hterms (m : ℤ) : Continuous (fun t : ℝ => scaledFourierCoeff g σ m * phase ((m : ℝ) * t)) := by
    unfold phase
    fun_prop
  apply continuous_tsum hterms (summable_scaledFourierCoeff g hσ).norm
  intro m t
  simp only [norm_mul, norm_phase, mul_one, le_refl]

lemma re_periodizedSchwartz_nonneg (g : 𝓢(ℝ, ℂ)) {σ : ℝ} (hσ : 0 < σ)
    (hg : ∀ x : ℝ, 0 ≤ (g x).re) (t : ℝ) : 0 ≤ (periodizedSchwartz g σ t).re := by
  rw [periodizedSchwartz, Complex.re_tsum (summable_periodizedSchwartz g hσ t)]
  exact tsum_nonneg (fun k => hg _)

lemma sum_periodized_samples_le_re {α : Type*} (g : 𝓢(ℝ, ℂ)) {σ : ℝ} (hσ : 0 < σ)
    (hg : ∀ x : ℝ, 0 ≤ (g x).re) (t : ℝ) (Y : Finset α) (k : α → ℤ)
    (hk : Set.InjOn k (Y : Set α)) :
    (∑ y ∈ Y, (g (σ⁻¹ * (t + k y))).re) ≤ (periodizedSchwartz g σ t).re := by
  have hs := summable_periodizedSchwartz g hσ t
  have hr : Summable (fun n : ℤ => (g (σ⁻¹ * (t + n))).re) := by
    apply hs.norm.of_norm_bounded
    intro n
    rw [Real.norm_eq_abs]
    exact Complex.abs_re_le_norm _
  classical
  calc
    _ = ∑ n ∈ Y.image k, (g (σ⁻¹ * (t + n))).re := (Finset.sum_image hk).symm
    _ ≤ ∑' n : ℤ, (g (σ⁻¹ * (t + n))).re :=
      hr.sum_le_tsum (Y.image k) (fun n hn => hg _)
    _ = _ := (Complex.re_tsum hs).symm

lemma integrable_weighted_periodization (f g : 𝓢(ℝ, ℂ)) {δ σ : ℝ}
    (hδ : 0 < δ) (hσ : 0 < σ) (θ : ℝ → ℝ) (hθ : Continuous θ) :
    Integrable (fun x : ℝ => f (δ * x) * periodizedSchwartz g σ (θ x)) := by
  have hf : Integrable (fun x : ℝ => f (δ * x)) := by
    change Integrable (dilateSchwartz f δ hδ.ne' : ℝ → ℂ)
    exact (dilateSchwartz f δ hδ.ne').integrable
  have hcont : Continuous (fun x : ℝ => f (δ * x) * periodizedSchwartz g σ (θ x)) :=
    (f.continuous.comp (continuous_const.mul continuous_id)).mul
      ((continuous_periodizedSchwartz g hσ).comp hθ)
  apply (hf.norm.const_mul (∑' m : ℤ, ‖scaledFourierCoeff g σ m‖)).mono' hcont.aestronglyMeasurable
  filter_upwards [] with x
  rw [norm_mul]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left
    (norm_periodizedSchwartz_le g hσ (θ x)) (norm_nonneg (f (δ * x)))

lemma re_integral_weighted_periodization (f g : 𝓢(ℝ, ℂ)) {δ σ : ℝ}
    (hδ : 0 < δ) (hσ : 0 < σ) (θ : ℝ → ℝ) (hθ : Continuous θ)
    (hf : ∀ x : ℝ, (f x).im = 0) :
    (∫ x : ℝ, f (δ * x) * periodizedSchwartz g σ (θ x)).re =
      ∫ x : ℝ, (f (δ * x)).re * (periodizedSchwartz g σ (θ x)).re := by
  have hh := integral_re (𝕜 := ℂ) (integrable_weighted_periodization f g hδ hσ θ hθ)
  change (∫ x : ℝ, (f (δ * x) * periodizedSchwartz g σ (θ x)).re) =
    (∫ x : ℝ, f (δ * x) * periodizedSchwartz g σ (θ x)).re at hh
  rw [← hh]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [Complex.mul_re, hf, zero_mul, sub_zero]

end Erdos587
