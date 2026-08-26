import ErdosProblems.Erdos421.SchwartzDirichletWindows

/-! # Normalized rescaling of a Schwartz window and its Fourier transform -/

namespace Erdos421

open Complex MeasureTheory FourierTransform
open scoped SchwartzMap

noncomputable def normalizedSchwartzScale (δ : ℝ) (hδ : 0 < δ) (φ : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ) :=
  (δ⁻¹ : ℝ) • SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (LinearEquiv.smulOfNeZero ℝ ℝ δ⁻¹ (inv_ne_zero hδ.ne')).toContinuousLinearEquiv φ

theorem normalizedSchwartzScale_apply (δ : ℝ) (hδ : 0 < δ) (φ : 𝓢(ℝ, ℂ)) (x : ℝ) :
    normalizedSchwartzScale δ hδ φ x = (δ⁻¹ : ℝ) • φ (x / δ) := by
  simp only [normalizedSchwartzScale, smul_apply,
    SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply,
    LinearEquiv.coe_toContinuousLinearEquiv', LinearEquiv.smulOfNeZero_apply,
    smul_eq_mul, div_eq_mul_inv, mul_comm]

theorem fourier_normalized_rescale (δ : ℝ) (hδ : 0 < δ) (φ : ℝ → ℂ) (ξ : ℝ) :
    𝓕 (fun x : ℝ ↦ (δ⁻¹ : ℝ) • φ (x / δ)) ξ = 𝓕 φ (δ * ξ) := by
  let F : ℝ → ℂ := fun y ↦ Complex.exp ((-2 * Real.pi * (y * (δ * ξ)) : ℝ) * I) * φ y
  have hleft : 𝓕 (fun x : ℝ ↦ (δ⁻¹ : ℝ) • φ (x / δ)) ξ =
      (δ⁻¹ : ℝ) • ∫ x : ℝ, F (δ⁻¹ * x) := by
    rw [Real.fourier_eq', ← integral_smul]
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro x
    simp only [RCLike.inner_apply, RCLike.conj_to_real, smul_eq_mul, Complex.real_smul, F]
    have hx : δ⁻¹ * x = x / δ := by ring
    rw [hx]
    have he : (x / δ) * (δ * ξ) = ξ * x := by field_simp
    rw [he]
    ring
  have hright : 𝓕 φ (δ * ξ) = ∫ y : ℝ, F y := by
    rw [Real.fourier_eq']
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro y
    simp only [F, RCLike.inner_apply, RCLike.conj_to_real, smul_eq_mul]
    rw [mul_comm (δ * ξ) y]
  rw [hleft, Measure.integral_comp_inv_mul_left F δ, abs_of_pos hδ,
    smul_smul, inv_mul_cancel₀ hδ.ne', one_smul, hright]

theorem fourier_normalizedSchwartzScale (δ : ℝ) (hδ : 0 < δ) (φ : 𝓢(ℝ, ℂ)) (ξ : ℝ) :
    𝓕 (normalizedSchwartzScale δ hδ φ) ξ = 𝓕 φ (δ * ξ) := by
  have he : (normalizedSchwartzScale δ hδ φ : ℝ → ℂ) = fun x ↦ (δ⁻¹ : ℝ) • φ (x / δ) :=
    funext (normalizedSchwartzScale_apply δ hδ φ)
  simpa only [← he, SchwartzMap.fourier_coe] using!
    fourier_normalized_rescale δ hδ (φ : ℝ → ℂ) ξ

end Erdos421
