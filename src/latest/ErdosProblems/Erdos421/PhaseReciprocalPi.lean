import ErdosProblems.Erdos421.PhaseReciprocal

/-! # Reciprocal phase estimates over a half period -/

namespace Erdos421

open Complex MeasureTheory

theorem phase_sub_one_norm_lower_pi {x : ℝ} (hx : 0 < x) (hxpi : x ≤ Real.pi) :
    x / 2 ≤ ‖oscillatoryPhase 1 x - 1‖ := by
  have hsin : x / Real.pi ≤ Real.sin (x / 2) := by
    simpa using Real.mul_le_sin (x := x / 2) (by positivity) (by linarith)
  have hquarter : x / 4 ≤ x / Real.pi :=
    div_le_div_of_nonneg_left hx.le Real.pi_pos Real.pi_le_four
  have hnonneg : 0 ≤ 2 * Real.sin (x / 2) := by
    have hxpi' : (0 : ℝ) ≤ x / Real.pi := by positivity
    linarith
  simp only [oscillatoryPhase, Complex.ofReal_one, mul_one,
    Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs, abs_of_nonneg hnonneg]
  linarith

theorem phase_sub_one_ne_zero_pi {x : ℝ} (hx : 0 < x) (hxpi : x ≤ Real.pi) :
    oscillatoryPhase 1 x - 1 ≠ 0 := by
  have h := phase_sub_one_norm_lower_pi hx hxpi
  intro hz
  rw [hz, norm_zero] at h
  linarith

theorem phaseReciprocal_norm_le_pi {x : ℝ} (hx : 0 < x) (hxpi : x ≤ Real.pi) :
    ‖phaseReciprocal x‖ ≤ 2 / x := by
  have h := phase_sub_one_norm_lower_pi hx hxpi
  have hn : 0 < ‖oscillatoryPhase 1 x - 1‖ := (by linarith : 0 < x / 2).trans_le h
  rw [phaseReciprocal, norm_inv, inv_eq_one_div]
  apply (div_le_div_iff₀ hn hx).mpr
  linarith

theorem phaseReciprocal_hasDerivAt_pi {x : ℝ} (hx : 0 < x) (hxpi : x ≤ Real.pi) :
    HasDerivAt phaseReciprocal
      (-(Complex.I * oscillatoryPhase 1 x) / (oscillatoryPhase 1 x - 1) ^ 2) x := by
  have h := ((oscillatoryPhase_hasDerivAt 1 x).sub_const 1).fun_inv
    (phase_sub_one_ne_zero_pi hx hxpi)
  unfold phaseReciprocal
  simpa only [Complex.ofReal_one, mul_one] using! h

theorem phaseReciprocal_deriv_norm_le_pi {x : ℝ} (hx : 0 < x) (hxpi : x ≤ Real.pi) :
    ‖deriv phaseReciprocal x‖ ≤ 4 / x ^ 2 := by
  rw [(phaseReciprocal_hasDerivAt_pi hx hxpi).deriv, norm_div, norm_neg, norm_mul,
    Complex.norm_I, norm_oscillatoryPhase, one_mul, norm_pow]
  have h := phase_sub_one_norm_lower_pi hx hxpi
  have hn : 0 < ‖oscillatoryPhase 1 x - 1‖ := (by linarith : 0 < x / 2).trans_le h
  apply (div_le_div_iff₀ (sq_pos_of_pos hn) (sq_pos_of_pos hx)).mpr
  nlinarith [norm_nonneg (oscillatoryPhase 1 x - 1)]

theorem phaseReciprocal_variation_pi {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ Real.pi) :
    ‖phaseReciprocal b - phaseReciprocal a‖ ≤ 4 / a - 4 / b := by
  have hder : ∀ x ∈ Set.Icc a b, DifferentiableAt ℝ phaseReciprocal x := by
    intro x hx
    exact (phaseReciprocal_hasDerivAt_pi (ha.trans_le hx.1) (hx.2.trans hb)).differentiableAt
  have hcont : ContinuousOn phaseReciprocal (Set.Icc a b) :=
    fun x hx ↦ (hder x hx).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ phaseReciprocal (Set.Ioo a b) :=
    fun x hx ↦ (hder x ⟨hx.1.le, hx.2.le⟩).differentiableWithinAt
  have hbound : ∀ᵐ x, x ∈ Set.Ioo a b → ‖deriv phaseReciprocal x‖ ≤ 4 / x ^ 2 :=
    Filter.Eventually.of_forall (fun x hx ↦
      phaseReciprocal_deriv_norm_le_pi (ha.trans hx.1) (hx.2.le.trans hb))
  have hint : IntervalIntegrable (fun x : ℝ ↦ 4 / x ^ 2) volume a b := by
    apply ContinuousOn.intervalIntegrable
    apply continuousOn_const.div (continuousOn_id.pow 2)
    intro x hx
    rw [Set.uIcc_of_le hab] at hx
    exact pow_ne_zero 2 (ha.trans_le hx.1).ne'
  have h := norm_sub_le_integral_of_norm_deriv_le_of_le hab hcont hdiff hbound hint
  rwa [integral_four_div_sq ha hab] at h

end Erdos421
