import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Topology.UnitInterval

/-!
# Nonvanishing interpolation of complex coefficients

Exponentiating the affine interpolation between two fixed complex logarithms
joins nonzero coefficients without meeting zero. When the endpoints lie in the
open unit disk, the entire interpolation stays in that disk.
-/

noncomputable section

namespace Wikipedia.HopfProblem.SpecialPeriods.EllipticAttachingMeridians

/-- Interpolate two fixed logarithms, then exponentiate. The logarithms do not
vary with the interval parameter, so their branch cut does not affect continuity. -/
def coefficientInterpolation (d a : ℂ) (s : unitInterval) : ℂ :=
  Complex.exp (((1 - (s : ℝ) : ℝ) : ℂ) * Complex.log d +
    ((s : ℝ) : ℂ) * Complex.log a)

theorem coefficientInterpolation_continuous (d a : ℂ) :
    Continuous (coefficientInterpolation d a) := by
  unfold coefficientInterpolation
  exact Complex.continuous_exp.comp
    (((Complex.continuous_ofReal.comp
      (continuous_const.sub continuous_subtype_val)).mul continuous_const).add
      ((Complex.continuous_ofReal.comp continuous_subtype_val).mul continuous_const))

@[simp] theorem coefficientInterpolation_zero (d a : ℂ) (hd : d ≠ 0) :
    coefficientInterpolation d a 0 = d := by
  simpa [coefficientInterpolation] using Complex.exp_log hd

@[simp] theorem coefficientInterpolation_one (d a : ℂ) (ha : a ≠ 0) :
    coefficientInterpolation d a 1 = a := by
  simpa [coefficientInterpolation] using Complex.exp_log ha

theorem coefficientInterpolation_ne_zero (d a : ℂ) (s : unitInterval) :
    coefficientInterpolation d a s ≠ 0 :=
  Complex.exp_ne_zero _

theorem coefficientInterpolation_norm_lt_one (d a : ℂ) (s : unitInterval)
    (hd : d ≠ 0) (ha : a ≠ 0) (hdnorm : ‖d‖ < 1) (hanorm : ‖a‖ < 1) :
    ‖coefficientInterpolation d a s‖ < 1 := by
  have hdlog : Real.log ‖d‖ < 0 := Real.log_neg (norm_pos_iff.mpr hd) hdnorm
  have halog : Real.log ‖a‖ < 0 := Real.log_neg (norm_pos_iff.mpr ha) hanorm
  rw [coefficientInterpolation, Complex.norm_exp, Real.exp_lt_one_iff]
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, Complex.log_re]
  by_cases hs : (s : ℝ) = 0
  · simpa [hs] using hdlog
  · exact add_neg_of_nonpos_of_neg
      (mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr s.property.2) hdlog.le)
      (mul_neg_of_pos_of_neg (lt_of_le_of_ne s.property.1 (Ne.symm hs)) halog)

end Wikipedia.HopfProblem.SpecialPeriods.EllipticAttachingMeridians
