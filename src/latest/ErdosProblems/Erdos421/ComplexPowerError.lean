import ErdosProblems.Erdos421.ZetaBlocks
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-! # Local sum--integral errors for complex powers -/

namespace Erdos421

open MeasureTheory

theorem cpow_neg_lipschitz_right {a y : ℝ} (ha : 0 < a) (hay : a ≤ y)
    (s : ℂ) (hs : 0 < s.re) :
    ‖(y : ℂ) ^ (-s) - (a : ℂ) ^ (-s)‖ ≤
      ‖s‖ * a ^ (-s.re - 1) * (y - a) := by
  have hsne : -s ≠ 0 := by
    intro h
    have he := congrArg Complex.re h
    simp only [Complex.neg_re, Complex.zero_re] at he
    linarith
  have hd : ∀ x ∈ Set.Ici a,
      HasDerivWithinAt (fun x : ℝ ↦ (x : ℂ) ^ (-s))
        ((-s) * (x : ℂ) ^ (-s - 1)) (Set.Ici a) x := by
    intro x hx
    exact (hasDerivAt_ofReal_cpow_const (ha.trans_le hx).ne' hsne).hasDerivWithinAt
  have hderiv : ∀ x ∈ Set.Ici a,
      ‖(-s) * (x : ℂ) ^ (-s - 1)‖ ≤ ‖s‖ * a ^ (-s.re - 1) := by
    intro x hx
    rw [norm_mul, norm_neg, Complex.norm_cpow_eq_rpow_re_of_pos (ha.trans_le hx)]
    simp only [Complex.sub_re, Complex.neg_re, Complex.one_re]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos ha hx (by linarith)) (norm_nonneg s)
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hd hderiv
    (convex_Ici a) (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hay)
  simpa only [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hay)] using h

theorem cpow_neg_intervalIntegrable {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (s : ℂ) :
    IntervalIntegrable (fun x : ℝ ↦ (x : ℂ) ^ (-s)) volume a b := by
  apply ContinuousOn.intervalIntegrable_of_Icc hab
  intro x hx
  exact (Complex.continuousAt_ofReal_cpow_const x (-s)
    (Or.inr (ha.trans_le hx.1).ne')).continuousWithinAt

/-- The error over a unit interval is bounded by the initial derivative
size. This estimate is uniform in the imaginary part of `s`. -/
theorem cpow_unit_sum_integral_error {a : ℝ} (ha : 0 < a)
    (s : ℂ) (hs : 0 < s.re) :
    ‖(a : ℂ) ^ (-s) - ∫ x in a..a + 1, (x : ℂ) ^ (-s)‖ ≤
      ‖s‖ * a ^ (-s.re - 1) := by
  have hint := cpow_neg_intervalIntegrable ha (by linarith : a ≤ a + 1) s
  have he : (a : ℂ) ^ (-s) - ∫ x in a..a + 1, (x : ℂ) ^ (-s) =
      ∫ x in a..a + 1, ((a : ℂ) ^ (-s) - (x : ℂ) ^ (-s)) := by
    rw [intervalIntegral.integral_sub intervalIntegrable_const hint,
      intervalIntegral.integral_const]
    simp only [add_sub_cancel_left, one_smul]
  rw [he]
  have hbound : ∀ x ∈ Set.uIoc a (a + 1),
      ‖(a : ℂ) ^ (-s) - (x : ℂ) ^ (-s)‖ ≤ ‖s‖ * a ^ (-s.re - 1) := by
    intro x hx
    rw [Set.uIoc_of_le (by linarith)] at hx
    have hxlow := hx.1.le
    rw [norm_sub_rev]
    apply (cpow_neg_lipschitz_right ha hxlow s hs).trans
    have hc : 0 ≤ ‖s‖ * a ^ (-s.re - 1) := by positivity
    nlinarith [hx.2]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  simpa only [add_sub_cancel_left, abs_one, mul_one] using h

end Erdos421
