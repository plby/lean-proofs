import ErdosProblems.Erdos1002.GaussDenominatorMaximal

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# A reverse comparison between Gauss and uniform measure

The Gauss density on `(0,1]` is bounded above by `1 / log 2`.  This file
records the corresponding measurable-set estimate in both `ℝ≥0∞`- and
real-valued form.  It complements the opposite comparison used when
transferring Gauss-probability estimates to Lebesgue measure.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Erdos1002

noncomputable section

theorem gaussMeasure_le_inv_log_two_mul_uniform01Measure
    {s : Set ℝ} (hs : MeasurableSet s) :
    gaussMeasure s ≤
      ENNReal.ofReal (1 / Real.log 2) * uniform01Measure s := by
  have huniform :
      uniform01Measure = volume.restrict (Ioc (0 : ℝ) 1) := by
    calc
      uniform01Measure = volume.restrict (Ioo (0 : ℝ) 1) := rfl
      _ = volume.restrict (Ioc (0 : ℝ) 1) :=
        restrict_Ioo_eq_restrict_Ioc
  have hgauss :
      gaussMeasure =
        (volume.restrict (Ioc (0 : ℝ) 1)).withDensity
          gaussDensityCore := by
    rw [gaussMeasure_eq_volume_withDensity]
    exact
      MeasureTheory.withDensity_indicator
        measurableSet_Ioc gaussDensityCore
  rw [hgauss, MeasureTheory.withDensity_apply _ hs, huniform]
  calc
    (∫⁻ x in s, gaussDensityCore x
        ∂volume.restrict (Ioc (0 : ℝ) 1)) ≤
        ∫⁻ _x in s, ENNReal.ofReal (1 / Real.log 2)
          ∂volume.restrict (Ioc (0 : ℝ) 1) := by
      apply lintegral_mono_ae
      filter_upwards
        [ae_restrict_of_ae
          (ae_restrict_mem (μ := volume) measurableSet_Ioc)] with x hx
      unfold gaussDensityCore
      apply ENNReal.ofReal_le_ofReal
      have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
      have hden : 0 < Real.log 2 * (1 + x) := by
        exact mul_pos hlog (by linarith [hx.1])
      unfold gaussDensityReal
      apply (div_le_div_iff_of_pos_left one_pos hden hlog).2
      nlinarith [hx.1]
    _ = ENNReal.ofReal (1 / Real.log 2) *
        (volume.restrict (Ioc (0 : ℝ) 1)) s :=
      setLIntegral_const s _

theorem gaussMeasureReal_le_inv_log_two_mul_uniform01MeasureReal
    {s : Set ℝ} (hs : MeasurableSet s) :
    gaussMeasure.real s ≤
      (1 / Real.log 2) * uniform01Measure.real s := by
  have h :=
    gaussMeasure_le_inv_log_two_mul_uniform01Measure hs
  have hreal :=
    ENNReal.toReal_mono
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (measure_ne_top uniform01Measure s))
      h
  have hcoeff : 0 ≤ 1 / Real.log 2 := by positivity
  simpa only [measureReal_def, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hcoeff] using! hreal

end

end Erdos1002
