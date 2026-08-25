import Util.Bernays.HalfPlaneSquareBounds
import Mathlib.Analysis.Analytic.Order
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass

/-!
# Almost-everywhere boundary decay for square-root derivatives
-/

open Set Filter Topology MeasureTheory

namespace Bernays

theorem norm_eq_sqrt_norm_of_square {u v : ℂ} (heq : v = u ^ 2) :
    ‖u‖ = Real.sqrt ‖v‖ := by
  rw [heq, norm_pow, Real.sqrt_sq (norm_nonneg u)]

theorem halfPlane_square_deriv_formula {f F : ℂ → ℂ}
    (hf : ∀ z : ℂ, 1 < z.re → DifferentiableAt ℂ f z)
    (hF : ∀ z : ℂ, (1 / 2 : ℝ) < z.re → DifferentiableAt ℂ F z)
    (heq : ∀ z : ℂ, 1 < z.re → F z = f z ^ 2)
    {z : ℂ} (hz : 1 < z.re) (hne : F z ≠ 0) :
    ‖deriv f z‖ = ‖deriv F z‖ / (2 * Real.sqrt ‖F z‖) := by
  have hevent : F =ᶠ[𝓝 z] fun w => f w ^ 2 :=
    Filter.eventually_of_mem ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz) heq
  have hd := deriv_square_norm (hf z hz) (hF z (by linarith)) hevent
  rw [norm_eq_sqrt_norm_of_square (heq z hz)] at hd
  have hp : 0 < Real.sqrt ‖F z‖ := Real.sqrt_pos.mpr (norm_pos_iff.mpr hne)
  apply (eq_div_iff (mul_pos (by norm_num : (0 : ℝ) < 2) hp).ne').mpr
  linarith

theorem halfPlane_square_scaled_deriv_tendsto {f F : ℂ → ℂ}
    (hf : ∀ z : ℂ, 1 < z.re → DifferentiableAt ℂ f z)
    (hF : ∀ z : ℂ, (1 / 2 : ℝ) < z.re → DifferentiableAt ℂ F z)
    (heq : ∀ z : ℂ, 1 < z.re → F z = f z ^ 2)
    (t : ℝ) (hne : F (1 + t * Complex.I) ≠ 0) :
    Tendsto (fun δ : ℝ => Real.sqrt δ * ‖deriv f ((1 + δ : ℝ) + t * Complex.I)‖)
      (𝓝[>] 0) (𝓝 0) := by
  let z : ℝ → ℂ := fun δ => (1 + δ : ℝ) + t * Complex.I
  have hz : Tendsto z (𝓝[>] 0) (𝓝 (1 + t * Complex.I)) := by
    have hc : Continuous z := by dsimp only [z]; fun_prop
    simpa only [z, add_zero, Complex.ofReal_one] using
      (hc.continuousAt (x := 0)).tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi 0))
  have ht : (1 / 2 : ℝ) < (1 + t * Complex.I).re := by norm_num
  have hFcont := (hF _ ht).continuousAt.tendsto.comp hz
  have hF'cont := ((halfPlane_deriv_continuousOn hF).continuousAt
    ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds ht)).tendsto.comp hz
  have hden : 2 * Real.sqrt ‖F (1 + t * Complex.I)‖ ≠ 0 :=
    (mul_pos (by norm_num) (Real.sqrt_pos.mpr (norm_pos_iff.mpr hne))).ne'
  have hsqrt : Tendsto (fun δ : ℝ => Real.sqrt δ) (𝓝[>] 0) (𝓝 0) := by
    simpa only [Real.sqrt_zero] using (Real.continuous_sqrt.continuousAt (x := 0)).tendsto.mono_left
      (nhdsWithin_le_nhds (s := Ioi 0))
  have hlim := hsqrt.mul (hF'cont.norm.div ((hFcont.norm.sqrt).const_mul 2) hden)
  rw [zero_mul] at hlim
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin, hFcont.eventually_ne hne] with δ hδ hnonzero
  have hδ' : 1 < (z δ).re := by
    dsimp only [z]
    simpa using hδ
  rw [halfPlane_square_deriv_formula hf hF heq hδ' hnonzero]
  rfl

theorem halfPlane_boundary_zeros_countable {F : ℂ → ℂ}
    (hF : ∀ z : ℂ, (1 / 2 : ℝ) < z.re → DifferentiableAt ℂ F z)
    (hne : ∃ z : ℂ, (1 / 2 : ℝ) < z.re ∧ F z ≠ 0) :
    {t : ℝ | F (1 + t * Complex.I) = 0}.Countable := by
  obtain ⟨w, hw, hFw⟩ := hne
  let U := {z : ℂ | (1 / 2 : ℝ) < z.re}
  have hA : AnalyticOnNhd ℂ F U :=
    (halfPlane_differentiableOn hF).analyticOnNhd (isOpen_lt continuous_const Complex.continuous_re)
  have hU : IsConnected U := (convex_halfSpace_re_gt (1 / 2)).isConnected ⟨w, hw⟩
  have hdisc : IsDiscrete ((F ⁻¹' {0}) ∩ U) :=
    isDiscrete_of_codiscreteWithin (hA.preimage_zero_mem_codiscreteWithin hFw hw hU)
  have hc := (HereditarilyLindelofSpace.isLindelof _).countable_of_isDiscrete hdisc
  have hinj : Function.Injective (fun t : ℝ => (1 : ℂ) + t * Complex.I) := by
    intro t s h
    simpa using congrArg Complex.im h
  apply (hc.preimage hinj).mono
  intro t ht
  exact ⟨ht, by norm_num [U]⟩

theorem halfPlane_square_scaled_deriv_ae_tendsto {f F : ℂ → ℂ}
    (hf : ∀ z : ℂ, 1 < z.re → DifferentiableAt ℂ f z)
    (hF : ∀ z : ℂ, (1 / 2 : ℝ) < z.re → DifferentiableAt ℂ F z)
    (heq : ∀ z : ℂ, 1 < z.re → F z = f z ^ 2)
    (hne : ∃ z : ℂ, (1 / 2 : ℝ) < z.re ∧ F z ≠ 0) :
    ∀ᵐ t : ℝ, Tendsto (fun δ : ℝ => Real.sqrt δ * ‖deriv f ((1 + δ : ℝ) + t * Complex.I)‖)
      (𝓝[>] 0) (𝓝 0) := by
  have hnull := (halfPlane_boundary_zeros_countable hF hne).measure_zero (μ := volume)
  have hneae : ∀ᵐ t : ℝ, F (1 + t * Complex.I) ≠ 0 := by
    rw [ae_iff]
    simpa only [not_not] using hnull
  filter_upwards [hneae] with t ht
  exact halfPlane_square_scaled_deriv_tendsto hf hF heq t ht

end Bernays
