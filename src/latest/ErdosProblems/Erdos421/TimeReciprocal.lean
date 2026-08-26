import ErdosProblems.Erdos421.Sampling

/-! # Logarithmic integrals of reciprocal distances -/

namespace Erdos421

open MeasureTheory

noncomputable def inverseDistance (c x : ℝ) : ℝ := 1 / (1 + |x - c|)

theorem inverseDistance_continuous (c : ℝ) : Continuous (inverseDistance c) := by
  unfold inverseDistance
  apply continuous_const.div (continuous_const.add ((continuous_id.sub continuous_const).abs))
  intro x
  change (1 + |x - c| : ℝ) ≠ 0
  positivity

theorem inverseDistance_nonneg (c x : ℝ) : 0 ≤ inverseDistance c x := by
  unfold inverseDistance
  positivity

theorem integral_inverseDistance_right (c : ℝ) {U : ℝ} (hU : 0 ≤ U) :
    (∫ x in c..c + U, inverseDistance c x) = Real.log (1 + U) := by
  have hder : ∀ x ∈ Set.uIcc c (c + U),
      HasDerivAt (fun x ↦ Real.log (1 + x - c)) (inverseDistance c x) x := by
    intro x hx
    rw [Set.uIcc_of_le (by linarith : c ≤ c + U)] at hx
    have hpos : 0 < 1 + x - c := by linarith [hx.1]
    have h := (((hasDerivAt_id x).const_add 1).sub_const c).log hpos.ne'
    simpa only [inverseDistance, abs_of_nonneg (sub_nonneg.mpr hx.1), add_sub_assoc,
      id_eq] using! h
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hder
    ((inverseDistance_continuous c).intervalIntegrable c (c + U))
  have heq : 1 + (c + U) - c = 1 + U := by ring
  simpa only [heq, add_sub_cancel_right, Real.log_one, sub_zero] using h

theorem integral_inverseDistance_left (c : ℝ) {U : ℝ} (hU : 0 ≤ U) :
    (∫ x in c - U..c, inverseDistance c x) = Real.log (1 + U) := by
  have hder : ∀ x ∈ Set.uIcc (c - U) c,
      HasDerivAt (fun x ↦ -Real.log (1 + c - x)) (inverseDistance c x) x := by
    intro x hx
    rw [Set.uIcc_of_le (by linarith : c - U ≤ c)] at hx
    have hpos : 0 < 1 + c - x := by linarith [hx.2]
    have h := (((hasDerivAt_const x (1 + c)).sub (hasDerivAt_id x)).log hpos.ne').neg
    simpa only [inverseDistance, abs_of_nonpos (sub_nonpos.mpr hx.2),
      zero_sub, neg_div, neg_neg, neg_sub, add_sub_assoc, Pi.sub_apply, Pi.neg_apply,
      id_eq] using! h
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hder
    ((inverseDistance_continuous c).intervalIntegrable (c - U) c)
  have heq : 1 + c - (c - U) = 1 + U := by ring
  simpa only [heq, add_sub_cancel_right, Real.log_one, neg_zero, zero_sub, neg_neg] using h

theorem integral_inverseDistance_centered (c : ℝ) {U : ℝ} (hU : 0 ≤ U) :
    (∫ x in c - U..c + U, inverseDistance c x) = 2 * Real.log (1 + U) := by
  have hcont := inverseDistance_continuous c
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hcont.intervalIntegrable (c - U) c) (hcont.intervalIntegrable c (c + U)),
    integral_inverseDistance_left c hU, integral_inverseDistance_right c hU]
  ring

theorem inverseDistance_unit_evaluation (c a : ℝ) :
    inverseDistance c a ≤ 2 * ∫ x in a..a + 1, inverseDistance c x := by
  have hpoint : ∀ x ∈ Set.Icc a (a + 1), inverseDistance c a ≤ 2 * inverseDistance c x := by
    intro x hx
    have hdist : |x - c| ≤ |a - c| + 1 := by
      have htri := abs_add_le (x - a) (a - c)
      rw [sub_add_sub_cancel, abs_of_nonneg (sub_nonneg.mpr hx.1)] at htri
      linarith [hx.2]
    unfold inverseDistance
    rw [← mul_div_assoc, mul_one]
    apply (div_le_div_iff₀ (by positivity : 0 < 1 + |a - c|)
      (by positivity : 0 < 1 + |x - c|)).mpr
    nlinarith [abs_nonneg (a - c)]
  have h := intervalIntegral.integral_mono_on (μ := volume) (by linarith : a ≤ a + 1)
    (continuous_const.intervalIntegrable a (a + 1))
    ((continuous_const.mul (inverseDistance_continuous c)).intervalIntegrable a (a + 1)) hpoint
  simpa only [intervalIntegral.integral_const, add_sub_cancel_left, smul_eq_mul,
    one_mul, Pi.mul_apply, intervalIntegral.integral_const_mul] using h

end Erdos421
