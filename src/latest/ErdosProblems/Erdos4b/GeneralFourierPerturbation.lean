/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierL1Bounds

/-!
# Uniform multiplicative perturbations of bounded absolute integrals

An eventual uniform `L¹` bound, together with a uniformly small
measurable correction, preserves the limit of the integral.
-/

namespace Erdos4b

noncomputable section

open Filter MeasureTheory
open scoped Topology

theorem norm_integral_mul_sub_one_le
    {X : Type*} [MeasurableSpace X] (μ : Measure X) (F c : X → ℂ) {δ B : ℝ}
    (hF : Integrable F μ) (hδ : 0 ≤ δ) (hc : ∀ x, ‖c x - 1‖ ≤ δ)
    (hB : (∫ x, ‖F x‖ ∂μ) ≤ B) :
    ‖∫ x, (c x - 1) * F x ∂μ‖ ≤ δ * B := by
  calc
    _ ≤ ∫ x, δ * ‖F x‖ ∂μ := by
      apply norm_integral_le_of_norm_le (hF.norm.const_mul δ)
      exact ae_of_all _ fun x ↦ by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (hc x) (norm_nonneg _)
    _ = δ * ∫ x, ‖F x‖ ∂μ := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left hB hδ

theorem tendsto_integral_mul_of_uniform_correction
    {α X : Type*} [MeasurableSpace X] {l : Filter α}
    (μ : Measure X) (F c : α → X → ℂ) (δ : α → ℝ) {B : ℝ} {z : ℂ}
    (hF : ∀ᶠ a in l, Integrable (F a) μ)
    (hc : ∀ᶠ a in l, AEStronglyMeasurable (c a) μ)
    (hδ : ∀ᶠ a in l, 0 ≤ δ a)
    (hclose : ∀ᶠ a in l, ∀ x, ‖c a x - 1‖ ≤ δ a)
    (hB : ∀ᶠ a in l, (∫ x, ‖F a x‖ ∂μ) ≤ B)
    (hδlim : Tendsto δ l (𝓝 0))
    (hlim : Tendsto (fun a ↦ ∫ x, F a x ∂μ) l (𝓝 z)) :
    Tendsto (fun a ↦ ∫ x, c a x * F a x ∂μ) l (𝓝 z) := by
  have herr : ∀ᶠ a in l, Integrable (fun x ↦ (c a x - 1) * F a x) μ := by
    filter_upwards [hF, hc, hclose] with a hFa hca hcl
    exact hFa.bdd_mul (hca.sub aestronglyMeasurable_const) (ae_of_all _ hcl)
  have hzero : Tendsto (fun a ↦ ∫ x, (c a x - 1) * F a x ∂μ) l (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have hmajorant : Tendsto (fun a ↦ δ a * B) l (𝓝 0) := by
      simpa only [zero_mul] using hδlim.mul_const B
    apply squeeze_zero' (Eventually.of_forall fun a ↦ norm_nonneg _) _ hmajorant
    filter_upwards [hF, hδ, hclose, hB] with a hFa hδa hca hBa
    exact norm_integral_mul_sub_one_le μ (F a) (c a) hFa hδa hca hBa
  have htotal := hzero.add hlim
  simp only [zero_add] at htotal
  apply htotal.congr'
  filter_upwards [herr, hF] with a hea hFa
  rw [← integral_add hea hFa]
  apply integral_congr_ae
  filter_upwards [] with x
  ring

end

end Erdos4b
