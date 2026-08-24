import ErdosProblems.Erdos587.ChirpWeights
import ErdosProblems.Erdos587.FresnelTails

/-!
# Uniform quadrature for low-frequency chirps

The centered interval mean subtracts a discrete weighted mean. Poisson
summation replaces it by the integral mean with a uniformly bounded error.
-/

open MeasureTheory
open scoped BigOperators SchwartzMap FourierTransform

namespace Erdos587

lemma schwartz_quadrature_error_eq_fourier_tail (g : 𝓢(ℝ, ℂ)) {δ : ℝ} (hδ : 0 < δ) :
    (∑' n : ℤ, g (δ * n)) - (∫ x : ℝ, g (δ * x)) =
      (δ : ℂ)⁻¹ * ∑' k : ℤ, if k = 0 then 0 else 𝓕 g ((k : ℝ) / δ) := by
  have hF : Summable (fun k : ℤ => 𝓕 g ((k : ℝ) / δ)) := by
    have h := summable_schwartz_int (dilateSchwartz (𝓕 g) δ⁻¹ (inv_ne_zero hδ.ne'))
    simpa only [dilateSchwartz_apply, div_eq_mul_inv, mul_comm] using h
  have hsplit := hF.tsum_eq_add_tsum_ite (0 : ℤ)
  have hpoisson := poisson_arithmetic_progression g hδ 0
  simp only [zero_add, mul_zero, zero_div, phase_zero, one_mul] at hpoisson
  have hint : (∫ x : ℝ, g (δ * x)) = (δ : ℂ)⁻¹ * ∫ x : ℝ, g x := by
    have h := Measure.integral_comp_mul_left (g : ℝ → ℂ) δ
    simpa only [abs_inv, abs_of_pos hδ, Complex.real_smul, Complex.ofReal_inv] using h
  rw [hpoisson, hint, hsplit]
  simp only [Int.cast_zero, zero_div, SchwartzMap.fourier_coe, fourier_zero_eq_integral]
  ring

theorem exists_uniform_chirp_quadrature_bound (f : 𝓢(ℝ, ℂ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ A : ℝ, |A| ≤ 1 → ∀ δ : ℝ, 0 < δ →
      ‖(∑' n : ℤ, quadraticChirpMul A f (δ * n)) -
        (∫ x : ℝ, quadraticChirpMul A f (δ * x))‖ ≤ C * δ := by
  let T : 𝓢(ℝ, ℂ) →L[ℝ] 𝓢(ℝ, ℂ) := FourierTransform.fourierCLM ℝ 𝓢(ℝ, ℂ)
  obtain ⟨M, hM, hb⟩ := exists_uniform_linear_chirp_derivative_bound f T 2 0
  let Z : ℝ := ∑' k : ℤ, 1 / (k : ℝ) ^ 2
  have hZ : 0 ≤ Z := tsum_nonneg (fun k => by positivity)
  refine ⟨M * Z, mul_nonneg hM hZ, ?_⟩
  intro A hA δ hδ
  let g := quadraticChirpMul A f
  have hdecay (x : ℝ) : (1 + |x|) ^ 2 * ‖𝓕 g x‖ ≤ M := by
    simpa only [T, g, iteratedDeriv_zero, FourierTransform.fourierCLM_apply] using hb A hA x
  have htail := nonzero_lattice_tail_le_of_decay (fun x => (𝓕 g) x) M hM hdecay (inv_pos.mpr hδ)
  have hF : Summable (fun k : ℤ => 𝓕 g ((k : ℝ) / δ)) := by
    have h := summable_schwartz_int (dilateSchwartz (𝓕 g) δ⁻¹ (inv_ne_zero hδ.ne'))
    simpa only [dilateSchwartz_apply, div_eq_mul_inv, mul_comm] using h
  have hnorm : Summable (fun k : ℤ => ‖if k = 0 then 0 else 𝓕 g ((k : ℝ) / δ)‖) := by
    apply hF.norm.of_norm_bounded
    intro k
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    split_ifs <;> simp only [norm_zero, norm_nonneg, le_refl]
  change ‖(∑' n : ℤ, g (δ * n)) - (∫ x : ℝ, g (δ * x))‖ ≤ _
  rw [schwartz_quadrature_error_eq_fourier_tail g hδ, norm_mul, norm_inv,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδ]
  apply (mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm hnorm) (inv_nonneg.mpr hδ.le)).trans
  have htail' : (∑' k : ℤ, ‖if k = 0 then 0 else 𝓕 g ((k : ℝ) / δ)‖) ≤
      (M * Z) / (δ⁻¹) ^ 2 := by
    simpa only [Z, div_eq_mul_inv, mul_comm] using htail
  calc
    _ ≤ δ⁻¹ * ((M * Z) / (δ⁻¹) ^ 2) := mul_le_mul_of_nonneg_left htail' (inv_nonneg.mpr hδ.le)
    _ = (M * Z) * δ := by field_simp

end Erdos587
