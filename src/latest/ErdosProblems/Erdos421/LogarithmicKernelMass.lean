import ErdosProblems.Erdos421.LogarithmicBuchstab

/-! # Total mass of the logarithmic integer kernel -/

namespace Erdos421

open MeasureTheory

theorem logarithmicIntegerWeight_integrable {δ : ℝ} (hδ : 0 < δ) (n : ℕ) :
    Integrable (fun y ↦ logarithmicIntegerWeight δ y n) := by
  exact (((oneSidedSchwartzWindow.integrable.comp_div hδ.ne').comp_sub_right
    (Real.log n)).smul δ⁻¹).smul (n : ℝ)⁻¹

theorem logarithmicIntegerWeight_integral {δ : ℝ} (hδ : 0 < δ) (n : ℕ) :
    (∫ y : ℝ, logarithmicIntegerWeight δ y n) = (↑((n : ℝ)⁻¹) : ℂ) := by
  unfold logarithmicIntegerWeight
  rw [integral_smul, integral_smul,
    integral_sub_right_eq_self (fun y ↦ oneSidedSchwartzWindow (y / δ)) (Real.log n),
    Measure.integral_comp_div, abs_of_pos hδ, oneSidedSchwartzWindow_integral]
  rw [smul_smul δ⁻¹ δ, inv_mul_cancel₀ hδ.ne', one_smul]
  simp only [Complex.real_smul, mul_one]

theorem logarithmicIntegerWeight_re_integrable {δ : ℝ} (hδ : 0 < δ) (n : ℕ) :
    Integrable (fun y ↦ (logarithmicIntegerWeight δ y n).re) :=
  (logarithmicIntegerWeight_integrable hδ n).re

theorem logarithmicIntegerWeight_re_integral {δ : ℝ} (hδ : 0 < δ) (n : ℕ) :
    (∫ y : ℝ, (logarithmicIntegerWeight δ y n).re) = (n : ℝ)⁻¹ := by
  simpa only [RCLike.re_eq_complex_re, logarithmicIntegerWeight_integral hδ,
    Complex.ofReal_re] using integral_re (logarithmicIntegerWeight_integrable hδ n)

theorem logarithmicIntegerWeight_weighted_integral (S : Finset ℕ) (a : ℕ → ℝ)
    {δ : ℝ} (hδ : 0 < δ) :
    (∫ y : ℝ, ∑ n ∈ S, a n * (logarithmicIntegerWeight δ y n).re) =
      ∑ n ∈ S, a n / n := by
  rw [integral_finsetSum S (fun n _ ↦
    (logarithmicIntegerWeight_re_integrable hδ n).const_mul (a n))]
  apply Finset.sum_congr rfl
  intro n hn
  rw [integral_const_mul, logarithmicIntegerWeight_re_integral hδ, div_eq_mul_inv]

end Erdos421
