import Util.Bernays.HalfPlaneSquarePointwise
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Integral decay of a square root and its derivative on finite vertical segments
-/

open Set Filter Topology MeasureTheory

namespace Bernays

theorem halfPlane_vertical_continuous {f : ℂ → ℂ} {c σ : ℝ}
    (hf : ContinuousOn f {z : ℂ | c < z.re}) (hσ : c < σ) :
    Continuous (fun t : ℝ => f ((σ : ℂ) + t * Complex.I)) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  apply (hf.continuousAt ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds
    (by simpa using hσ))).comp
  fun_prop

theorem halfPlane_square_scaled_norm_tendsto {f F : ℂ → ℂ}
    (hF : ∀ z : ℂ, (1 / 2 : ℝ) < z.re → DifferentiableAt ℂ F z)
    (heq : ∀ z : ℂ, 1 < z.re → F z = f z ^ 2) (t : ℝ) :
    Tendsto (fun δ : ℝ => Real.sqrt δ * ‖f ((1 + δ : ℝ) + t * Complex.I)‖)
      (𝓝[>] 0) (𝓝 0) := by
  have hz : Tendsto (fun δ : ℝ => ((1 + δ : ℝ) : ℂ) + t * Complex.I)
      (𝓝[>] 0) (𝓝 (1 + t * Complex.I)) := by
    have hc : Continuous (fun δ : ℝ => ((1 + δ : ℝ) : ℂ) + t * Complex.I) := by fun_prop
    simpa only [add_zero, Complex.ofReal_one] using
      (hc.continuousAt (x := 0)).tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi 0))
  have hcont := ((hF _ (by norm_num : (1 / 2 : ℝ) < (1 + t * Complex.I).re)).continuousAt.tendsto.comp hz).norm.sqrt
  have hsqrt : Tendsto (fun δ : ℝ => Real.sqrt δ) (𝓝[>] 0) (𝓝 0) := by
    simpa only [Real.sqrt_zero] using (Real.continuous_sqrt.continuousAt (x := 0)).tendsto.mono_left
      (nhdsWithin_le_nhds (s := Ioi 0))
  have hlim := hsqrt.mul hcont
  rw [zero_mul] at hlim
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  rw [norm_eq_sqrt_norm_of_square (heq _ (by simpa using hδ))]
  rfl

theorem halfPlane_square_scaled_deriv_integral_tendsto {f F : ℂ → ℂ}
    (hf : ∀ z : ℂ, 1 < z.re → DifferentiableAt ℂ f z)
    (hF : ∀ z : ℂ, (1 / 2 : ℝ) < z.re → DifferentiableAt ℂ F z)
    (heq : ∀ z : ℂ, 1 < z.re → F z = f z ^ 2)
    (hne : ∃ z : ℂ, (1 / 2 : ℝ) < z.re ∧ F z ≠ 0) (T : ℝ) :
    Tendsto (fun δ : ℝ => ∫ t : ℝ in Icc (-T) T,
      Real.sqrt δ * ‖deriv f ((1 + δ : ℝ) + t * Complex.I)‖)
      (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨K, _, hK⟩ := halfPlane_square_uniform_bounds hf hF heq T
  have hmeas : ∀ᶠ δ : ℝ in 𝓝[>] 0, AEStronglyMeasurable
      (fun t : ℝ => Real.sqrt δ * ‖deriv f ((1 + δ : ℝ) + t * Complex.I)‖)
      (volume.restrict (Icc (-T) T)) := by
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact ((halfPlane_vertical_continuous (halfPlane_deriv_continuousOn hf)
      (by simpa using hδ : 1 < 1 + δ)).norm.const_mul _).aestronglyMeasurable
  have hbound : ∀ᶠ δ : ℝ in 𝓝[>] 0, ∀ᵐ t : ℝ ∂volume.restrict (Icc (-T) T),
      ‖Real.sqrt δ * ‖deriv f ((1 + δ : ℝ) + t * Complex.I)‖‖ ≤ K := by
    filter_upwards [self_mem_nhdsWithin, (eventually_le_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono
      nhdsWithin_le_nhds] with δ hδ hδ₁
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    rw [Real.norm_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))]
    exact (hK δ t hδ hδ₁ (abs_le.mpr ht)).2
  have hlim := ae_restrict_of_ae (s := Icc (-T) T)
    (halfPlane_square_scaled_deriv_ae_tendsto hf hF heq hne)
  have h := tendsto_integral_filter_of_dominated_convergence (fun _ : ℝ => K) hmeas hbound
    (integrableOn_const isCompact_Icc.measure_ne_top) hlim
  simpa only [integral_zero] using h

theorem halfPlane_square_scaled_norm_integral_tendsto {f F : ℂ → ℂ}
    (hf : ∀ z : ℂ, 1 < z.re → DifferentiableAt ℂ f z)
    (hF : ∀ z : ℂ, (1 / 2 : ℝ) < z.re → DifferentiableAt ℂ F z)
    (heq : ∀ z : ℂ, 1 < z.re → F z = f z ^ 2) (T : ℝ) :
    Tendsto (fun δ : ℝ => ∫ t : ℝ in Icc (-T) T,
      Real.sqrt δ * ‖f ((1 + δ : ℝ) + t * Complex.I)‖)
      (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨K, hKpos, hK⟩ := halfPlane_square_uniform_bounds hf hF heq T
  have hmeas : ∀ᶠ δ : ℝ in 𝓝[>] 0, AEStronglyMeasurable
      (fun t : ℝ => Real.sqrt δ * ‖f ((1 + δ : ℝ) + t * Complex.I)‖)
      (volume.restrict (Icc (-T) T)) := by
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact ((halfPlane_vertical_continuous (halfPlane_differentiableOn hf).continuousOn
      (by simpa using hδ : 1 < 1 + δ)).norm.const_mul _).aestronglyMeasurable
  have hbound : ∀ᶠ δ : ℝ in 𝓝[>] 0, ∀ᵐ t : ℝ ∂volume.restrict (Icc (-T) T),
      ‖Real.sqrt δ * ‖f ((1 + δ : ℝ) + t * Complex.I)‖‖ ≤ K := by
    filter_upwards [self_mem_nhdsWithin, (eventually_le_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono
      nhdsWithin_le_nhds] with δ hδ hδ₁
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    rw [Real.norm_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))]
    have hsqrt : Real.sqrt δ ≤ 1 := by simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hδ₁
    calc
      _ ≤ Real.sqrt δ * K := mul_le_mul_of_nonneg_left (hK δ t hδ hδ₁ (abs_le.mpr ht)).1
        (Real.sqrt_nonneg _)
      _ ≤ K := by nlinarith
  have hlim : ∀ᵐ t : ℝ ∂volume.restrict (Icc (-T) T),
      Tendsto (fun δ : ℝ => Real.sqrt δ * ‖f ((1 + δ : ℝ) + t * Complex.I)‖)
        (𝓝[>] 0) (𝓝 0) := Eventually.of_forall (halfPlane_square_scaled_norm_tendsto hF heq)
  have h := tendsto_integral_filter_of_dominated_convergence (fun _ : ℝ => K) hmeas hbound
    (integrableOn_const isCompact_Icc.measure_ne_top) hlim
  simpa only [integral_zero] using h

end Bernays
