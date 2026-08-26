import ErdosProblems.Erdos421.LargeValues
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! # Reciprocal phase bounds for the first-derivative exponential-sum test -/

namespace Erdos421

open Complex MeasureTheory

noncomputable def phaseReciprocal (x : ℝ) : ℂ := (oscillatoryPhase 1 x - 1)⁻¹

theorem phase_sub_one_norm_lower {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) :
    x / 2 ≤ ‖oscillatoryPhase 1 x - 1‖ := by
  have hsq : x ^ 2 ≤ 1 := pow_le_one₀ hx.le hx1
  have hcube := mul_le_mul_of_nonneg_left hsq hx.le
  have hsin : x / 2 ≤ Real.sin x := by nlinarith [Real.sin_ge_sub_cube hx.le]
  have him : (oscillatoryPhase 1 x - 1).im = Real.sin x := by
    simp [oscillatoryPhase, Complex.exp_im]
  have hnorm := Complex.im_le_norm (oscillatoryPhase 1 x - 1)
  rw [him] at hnorm
  exact hsin.trans hnorm

theorem phase_sub_one_ne_zero {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) :
    oscillatoryPhase 1 x - 1 ≠ 0 := by
  have h := phase_sub_one_norm_lower hx hx1
  intro hz
  rw [hz, norm_zero] at h
  linarith

theorem phaseReciprocal_norm_le {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) :
    ‖phaseReciprocal x‖ ≤ 2 / x := by
  have h := phase_sub_one_norm_lower hx hx1
  have hnorm : 0 < ‖oscillatoryPhase 1 x - 1‖ := (by linarith : 0 < x / 2).trans_le h
  rw [phaseReciprocal, norm_inv, inv_eq_one_div]
  apply (div_le_div_iff₀ hnorm hx).mpr
  linarith

theorem phaseReciprocal_hasDerivAt {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) :
    HasDerivAt phaseReciprocal
      (-(Complex.I * oscillatoryPhase 1 x) / (oscillatoryPhase 1 x - 1) ^ 2) x := by
  have h := ((oscillatoryPhase_hasDerivAt 1 x).sub_const 1).fun_inv
    (phase_sub_one_ne_zero hx hx1)
  unfold phaseReciprocal
  simpa only [Complex.ofReal_one, mul_one] using! h

theorem phaseReciprocal_deriv_norm_le {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) :
    ‖deriv phaseReciprocal x‖ ≤ 4 / x ^ 2 := by
  rw [(phaseReciprocal_hasDerivAt hx hx1).deriv, norm_div, norm_neg, norm_mul,
    Complex.norm_I, norm_oscillatoryPhase, one_mul, norm_pow]
  have h := phase_sub_one_norm_lower hx hx1
  have hnorm : 0 < ‖oscillatoryPhase 1 x - 1‖ := (by linarith : 0 < x / 2).trans_le h
  apply (div_le_div_iff₀ (sq_pos_of_pos hnorm) (sq_pos_of_pos hx)).mpr
  nlinarith [norm_nonneg (oscillatoryPhase 1 x - 1)]

theorem integral_four_div_sq {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ x in a..b, 4 / x ^ 2) = 4 / a - 4 / b := by
  have hzero : (0 : ℝ) ∉ Set.uIcc a b := by
    rw [Set.uIcc_of_le hab]
    intro h
    exact ha.not_ge h.1
  have h := integral_zpow (a := a) (b := b) (n := (-2 : ℤ)) (Or.inr ⟨by norm_num, hzero⟩)
  have hf : (fun x : ℝ ↦ 4 / x ^ 2) = fun x ↦ 4 * x ^ (-2 : ℤ) := by
    ext x
    simp only [zpow_neg, zpow_ofNat, div_eq_mul_inv]
  rw [hf, intervalIntegral.integral_const_mul, h]
  norm_num [div_eq_mul_inv]
  ring

/-- The variation of the reciprocal phase is controlled by a telescoping inverse. -/
theorem phaseReciprocal_variation {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ 1) :
    ‖phaseReciprocal b - phaseReciprocal a‖ ≤ 4 / a - 4 / b := by
  have hder : ∀ x ∈ Set.Icc a b, DifferentiableAt ℝ phaseReciprocal x := by
    intro x hx
    exact (phaseReciprocal_hasDerivAt (ha.trans_le hx.1) (hx.2.trans hb)).differentiableAt
  have hcont : ContinuousOn phaseReciprocal (Set.Icc a b) :=
    fun x hx ↦ (hder x hx).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ phaseReciprocal (Set.Ioo a b) :=
    fun x hx ↦ (hder x ⟨hx.1.le, hx.2.le⟩).differentiableWithinAt
  have hbound : ∀ᵐ x, x ∈ Set.Ioo a b → ‖deriv phaseReciprocal x‖ ≤ 4 / x ^ 2 :=
    Filter.Eventually.of_forall (fun x hx ↦
      phaseReciprocal_deriv_norm_le (ha.trans hx.1) (hx.2.le.trans hb))
  have hint : IntervalIntegrable (fun x : ℝ ↦ 4 / x ^ 2) volume a b := by
    apply ContinuousOn.intervalIntegrable
    apply continuousOn_const.div (continuousOn_id.pow 2)
    intro x hx
    rw [Set.uIcc_of_le hab] at hx
    exact pow_ne_zero 2 (ha.trans_le hx.1).ne'
  have h := norm_sub_le_integral_of_norm_deriv_le_of_le hab hcont hdiff hbound hint
  rwa [integral_four_div_sq ha hab] at h

end Erdos421
