import ErdosProblems.Erdos1038.CircleFourier
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Exact cosine integrals on centered arcs

These elementary identities evaluate every Fourier mode on the centered
intervals used in the circle block argument.
-/

set_option warningAsError false

open MeasureTheory

namespace Erdos1038

noncomputable section

lemma integral_cos_mul_centered {m Q : ℝ} (hm : m ≠ 0) :
    (∫ x : ℝ in -Q..Q, Real.cos (m * x)) =
      2 * Real.sin (m * Q) / m := by
  rw [intervalIntegral.integral_comp_mul_left Real.cos hm,
    integral_cos]
  rw [show m * -Q = -(m * Q) by ring, Real.sin_neg]
  simp only [smul_eq_mul, sub_neg_eq_add, div_eq_mul_inv]
  ring

lemma integral_sin_mul_centered {m Q : ℝ} (hm : m ≠ 0) :
    (∫ x : ℝ in -Q..Q, Real.sin (m * x)) = 0 := by
  rw [intervalIntegral.integral_comp_mul_left Real.sin hm,
    integral_sin]
  rw [show m * -Q = -(m * Q) by ring, Real.cos_neg]
  simp

lemma integral_cos_positiveFrequency_centered (n : ℕ) {Q : ℝ}
    (hQ : Q ≠ 0) :
    (∫ x : ℝ in -Q..Q,
      Real.cos (((n + 1 : ℕ) : ℝ) * x)) =
      2 * Q * Real.sinc (((n + 1 : ℕ) : ℝ) * Q) := by
  have hm : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  rw [integral_cos_mul_centered hm, Real.sinc_of_ne_zero (mul_ne_zero hm hQ)]
  field_simp [hm]

lemma integral_sin_positiveFrequency_centered (n : ℕ) (Q : ℝ) :
    (∫ x : ℝ in -Q..Q,
      Real.sin (((n + 1 : ℕ) : ℝ) * x)) = 0 := by
  exact integral_sin_mul_centered (by positivity)

lemma integral_cos_frequency_sub_centered
    {m theta R : ℝ} (hm : m ≠ 0) :
    (∫ phi : ℝ in -R..R, Real.cos (m * (theta - phi))) =
      Real.cos (m * theta) * (2 * Real.sin (m * R) / m) := by
  have hcos : IntervalIntegrable (fun phi : ℝ ↦ Real.cos (m * phi))
      volume (-R) R := by
    simpa only [Function.comp_apply, id_eq] using!
      (Real.continuous_cos.comp
        (continuous_const.mul continuous_id)).intervalIntegrable (-R) R
  have hsin : IntervalIntegrable (fun phi : ℝ ↦ Real.sin (m * phi))
      volume (-R) R := by
    simpa only [Function.comp_apply, id_eq] using!
      (Real.continuous_sin.comp
        (continuous_const.mul continuous_id)).intervalIntegrable (-R) R
  have hpoint : (fun phi : ℝ ↦ Real.cos (m * (theta - phi))) =
      fun phi ↦ Real.cos (m * theta) * Real.cos (m * phi) +
        Real.sin (m * theta) * Real.sin (m * phi) := by
    funext phi
    rw [mul_sub, Real.cos_sub]
  rw [hpoint, intervalIntegral.integral_add
    (hcos.const_mul _) (hsin.const_mul _),
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    integral_cos_mul_centered hm, integral_sin_mul_centered hm]
  ring

lemma iteratedIntegral_cos_frequency_sub_centered
    {m Q R : ℝ} (hm : m ≠ 0) :
    (∫ theta : ℝ in -Q..Q,
      ∫ phi : ℝ in -R..R, Real.cos (m * (theta - phi))) =
      (2 * Real.sin (m * Q) / m) *
        (2 * Real.sin (m * R) / m) := by
  simp_rw [integral_cos_frequency_sub_centered hm]
  rw [intervalIntegral.integral_mul_const,
    integral_cos_mul_centered hm]

lemma iteratedIntegral_cos_positiveFrequency_sub_centered
    (n : ℕ) {Q R : ℝ} (hQ : Q ≠ 0) (hR : R ≠ 0) :
    (∫ theta : ℝ in -Q..Q,
      ∫ phi : ℝ in -R..R,
        Real.cos (((n + 1 : ℕ) : ℝ) * (theta - phi))) =
      4 * Q * R *
        (Real.sinc (((n + 1 : ℕ) : ℝ) * Q) *
          Real.sinc (((n + 1 : ℕ) : ℝ) * R)) := by
  have hm : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  rw [iteratedIntegral_cos_frequency_sub_centered hm,
    Real.sinc_of_ne_zero (mul_ne_zero hm hQ),
    Real.sinc_of_ne_zero (mul_ne_zero hm hR)]
  field_simp [hm]
  ring

end

end Erdos1038
