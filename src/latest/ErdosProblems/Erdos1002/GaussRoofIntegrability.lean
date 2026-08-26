import ErdosProblems.Erdos1002.GaussLebesgueTransfer
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Integrability of the Gauss roof observable

This file proves the measure-theoretic input needed before any ergodic or
mixing argument is applied to the roof `x ↦ -log x`.  In particular, the
singularity at zero is not hidden behind an informal appeal to a standard
continued-fraction theorem.
-/

open Filter MeasureTheory Set
open scoped ENNReal Topology Interval

namespace Erdos1002

noncomputable section

/-- The real-valued density obtained from `gaussDensity` is exactly the
supported real Gauss density. -/
theorem gaussDensity_toReal_eq_indicator :
    (fun x : ℝ ↦ (gaussDensity x).toReal) =
      (Ioc (0 : ℝ) 1).indicator gaussDensityReal := by
  funext x
  by_cases hx : x ∈ Ioc (0 : ℝ) 1
  · rw [indicator_of_mem hx]
    simp only [gaussDensity, indicator_of_mem hx, gaussDensityCore]
    rw [ENNReal.toReal_ofReal (gaussDensityReal_nonneg_on_unit hx)]
  · rw [indicator_of_notMem hx]
    simp [gaussDensity, hx]

/-- The logarithmic singularity is integrable on the half-open unit
interval with respect to Lebesgue measure. -/
theorem integrableOn_neg_log_Ioc_unit :
    IntegrableOn (fun x : ℝ ↦ -Real.log x) (Ioc 0 1) volume := by
  have hlog : IntervalIntegrable Real.log volume (0 : ℝ) 1 :=
    intervalIntegral.intervalIntegrable_log'
  have hlogOn : IntegrableOn Real.log (Ioc (0 : ℝ) 1) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mp hlog
  exact hlogOn.neg

/-- The roof observable `-log x` is genuinely Bochner-integrable under the
invariant Gauss probability. -/
theorem integrable_neg_log_gaussMeasure :
    Integrable (fun x : ℝ ↦ -Real.log x) gaussMeasure := by
  rw [gaussMeasure_eq_volume_withDensity,
    integrable_withDensity_iff measurable_gaussDensity]
  · have hdensity (x : ℝ) :
        (gaussDensity x).toReal =
          (Ioc (0 : ℝ) 1).indicator gaussDensityReal x :=
      congrFun gaussDensity_toReal_eq_indicator x
    simp_rw [hdensity]
    have hlogOn := integrableOn_neg_log_Ioc_unit
    have hmajor : Integrable
        ((Ioc (0 : ℝ) 1).indicator
          (fun x : ℝ ↦ (1 / Real.log 2) * |Real.log x|)) volume := by
      have habs : IntegrableOn (fun x : ℝ ↦ |Real.log x|)
          (Ioc 0 1) volume := by
        change Integrable (fun x : ℝ ↦ |Real.log x|)
          (volume.restrict (Ioc 0 1))
        simpa only [Real.norm_eq_abs, abs_neg] using! hlogOn.norm
      have hscaled : IntegrableOn
          (fun x : ℝ ↦ (1 / Real.log 2) * |Real.log x|)
          (Ioc 0 1) volume :=
        habs.const_mul (1 / Real.log 2)
      exact IntegrableOn.integrable_indicator hscaled measurableSet_Ioc
    apply Integrable.mono hmajor
    · exact ((Real.measurable_log.neg.mul
        (measurable_gaussDensityReal.indicator measurableSet_Ioc))).aestronglyMeasurable
    · filter_upwards with x
      by_cases hx : x ∈ Ioc (0 : ℝ) 1
      · rw [indicator_of_mem hx, indicator_of_mem hx]
        have hlogPos : 0 < Real.log 2 := Real.log_pos (by norm_num)
        have hxOne : 1 ≤ 1 + x := by linarith [hx.1]
        have hdenPos : 0 < Real.log 2 * (1 + x) := by positivity
        have hdensityNonneg : 0 ≤ gaussDensityReal x :=
          gaussDensityReal_nonneg_on_unit hx
        have hdensityLe : gaussDensityReal x ≤ 1 / Real.log 2 := by
          unfold gaussDensityReal
          apply (div_le_div_iff_of_pos_left one_pos hdenPos hlogPos).mpr
          nlinarith
        simp only [Real.norm_eq_abs, abs_mul, abs_neg, abs_abs,
          abs_of_nonneg hdensityNonneg,
          abs_of_nonneg (one_div_nonneg.mpr hlogPos.le)]
        simpa only [mul_comm] using!
          (mul_le_mul_of_nonneg_left hdensityLe (abs_nonneg (Real.log x)))
      · rw [indicator_of_notMem hx, indicator_of_notMem hx]
        simp
  · exact Eventually.of_forall fun x ↦ by
      by_cases hx : x ∈ Ioc (0 : ℝ) 1
      · rw [gaussDensity_eq_ofReal_on_unit hx]
        simp
      · simp [gaussDensity, hx]

/-- The Gauss roof has a finite, nonnegative expectation. -/
def gaussRoofMean : ℝ :=
  ∫ x : ℝ, -Real.log x ∂gaussMeasure

theorem gaussRoofMean_nonneg : 0 ≤ gaussRoofMean := by
  unfold gaussRoofMean
  apply integral_nonneg_of_ae
  filter_upwards [gaussMeasure_unit_ae] with x hx
  exact neg_nonneg.mpr (Real.log_nonpos hx.1.le hx.2)

end

end Erdos1002
