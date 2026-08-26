import ErdosProblems.Erdos1002.GaussDynamics
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Measure.WithDensity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Transfer between Gauss and Lebesgue measure

This file records the change of measure used when a continued-fraction
argument is first proved under the invariant Gauss probability and is then
transferred to Lebesgue measure.  All densities are supported explicitly on
`(0,1]`; thus the statements are equalities of measures on the whole real
line, rather than informal density identities valid only in the interior.
-/

open Filter MeasureTheory Set
open scoped ENNReal Topology Interval

namespace Erdos1002

noncomputable section

/-- The real Gauss density before restriction to the unit interval. -/
def gaussDensityReal (x : ℝ) : ℝ :=
  1 / (Real.log 2 * (1 + x))

/-- The unrestricted `ℝ≥0∞`-valued version of the reciprocal density. -/
def gaussDensityCore (x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (gaussDensityReal x)

/-- The Gauss density with respect to Lebesgue measure on the whole real
line.  The indicator makes its support, including the harmless endpoint
convention, explicit. -/
def gaussDensity (x : ℝ) : ℝ≥0∞ :=
  (Ioc (0 : ℝ) 1).indicator gaussDensityCore x

/-- The Radon--Nikodym weight which transfers Gauss expectations to
Lebesgue expectations on the unit interval. -/
def lebesgueOverGaussDensityReal (x : ℝ) : ℝ :=
  Real.log 2 * (1 + x)

/-- The preceding transfer weight as an `ℝ≥0∞`-valued density. -/
def lebesgueOverGaussDensity (x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (lebesgueOverGaussDensityReal x)

theorem measurable_gaussDensityReal : Measurable gaussDensityReal := by
  unfold gaussDensityReal
  fun_prop

theorem measurable_gaussDensity : Measurable gaussDensity := by
  unfold gaussDensity gaussDensityCore
  exact measurable_gaussDensityReal.ennreal_ofReal.indicator measurableSet_Ioc

theorem measurable_gaussDensityCore : Measurable gaussDensityCore := by
  unfold gaussDensityCore
  exact measurable_gaussDensityReal.ennreal_ofReal

theorem continuous_lebesgueOverGaussDensityReal :
    Continuous lebesgueOverGaussDensityReal := by
  unfold lebesgueOverGaussDensityReal
  fun_prop

theorem measurable_lebesgueOverGaussDensityReal :
    Measurable lebesgueOverGaussDensityReal :=
  continuous_lebesgueOverGaussDensityReal.measurable

theorem measurable_lebesgueOverGaussDensity :
    Measurable lebesgueOverGaussDensity := by
  exact measurable_lebesgueOverGaussDensityReal.ennreal_ofReal

/-- On the state space, the transfer weight is bounded above and below by
the sharp endpoint values. -/
theorem lebesgueOverGaussDensityReal_bounds {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) :
    Real.log 2 ≤ lebesgueOverGaussDensityReal x ∧
      lebesgueOverGaussDensityReal x ≤ 2 * Real.log 2 := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold lebesgueOverGaussDensityReal
  constructor <;> nlinarith [hx.1, hx.2]

theorem gaussDensityReal_nonneg_on_unit {x : ℝ}
    (hx : x ∈ Ioc (0 : ℝ) 1) : 0 ≤ gaussDensityReal x := by
  unfold gaussDensityReal
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hden : 0 < Real.log 2 * (1 + x) := mul_pos hlog (by linarith [hx.1])
  exact (one_div_nonneg.mpr hden.le)

private theorem integral_gaussDensityReal_Ioc {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) :
    ∫ x in a..b, gaussDensityReal x =
      (Real.log (1 + b) - Real.log (1 + a)) / Real.log 2 := by
  unfold gaussDensityReal
  have hlog : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  calc
    ∫ x in a..b, 1 / (Real.log 2 * (1 + x))
        = (Real.log 2)⁻¹ * ∫ x in a..b, (1 + x)⁻¹ := by
            rw [← intervalIntegral.integral_const_mul]
            apply intervalIntegral.integral_congr
            intro x _
            field_simp
    _ = (Real.log 2)⁻¹ *
        (Real.log (1 + b) - Real.log (1 + a)) := by
          rw [intervalIntegral.integral_comp_add_left,
            integral_inv_of_pos]
          · rw [Real.log_div (ne_of_gt (by linarith))
              (ne_of_gt (by linarith))]
          · linarith
          · linarith
    _ = (Real.log (1 + b) - Real.log (1 + a)) / Real.log 2 := by
          field_simp

private theorem intervalIntegrable_gaussDensityReal {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable gaussDensityReal volume a b := by
  apply ContinuousOn.intervalIntegrable_of_Icc hab
  intro x hx
  apply ContinuousAt.continuousWithinAt
  unfold gaussDensityReal
  have hxpos : 0 < 1 + x := by linarith [ha, hx.1]
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hden : Real.log 2 * (1 + x) ≠ 0 := ne_of_gt (mul_pos hlog hxpos)
  exact continuousAt_const.div
    (continuousAt_const.mul (continuousAt_const.add continuousAt_id)) hden

private theorem lintegral_gaussDensityCore_Ioc {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    ∫⁻ x in Ioc a b, gaussDensityCore x ∂volume =
      ENNReal.ofReal
        ((Real.log (1 + b) - Real.log (1 + a)) / Real.log 2) := by
  have hint : IntegrableOn gaussDensityReal (Ioc a b) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp
      (intervalIntegrable_gaussDensityReal ha hab)
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioc a b)] gaussDensityReal := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    apply gaussDensityReal_nonneg_on_unit
    exact ⟨ha.trans_lt hx.1, hx.2.trans hb⟩
  unfold gaussDensityCore
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnonneg,
    ← intervalIntegral.integral_of_le hab,
    integral_gaussDensityReal_Ioc ha hab]

private theorem gaussMeasure_Iic_eq_ofReal_gaussCDF (x : ℝ) :
    gaussMeasure (Iic x) = ENNReal.ofReal (gaussCDF x) := by
  rw [gaussMeasure, gaussStieltjes.measure_Iic tendsto_gaussCDF_atBot]
  change ENNReal.ofReal (gaussCDF x - 0) = ENNReal.ofReal (gaussCDF x)
  simp

/-- The Gauss probability measure has density
`1 / (log 2 * (1+x))` with respect to Lebesgue measure on `(0,1]`, and zero
density off that interval.  This is an equality of measures on `ℝ`. -/
theorem gaussMeasure_eq_volume_withDensity :
    gaussMeasure = volume.withDensity gaussDensity := by
  rw [show volume.withDensity gaussDensity =
      (volume.restrict (Ioc (0 : ℝ) 1)).withDensity gaussDensityCore by
    exact MeasureTheory.withDensity_indicator measurableSet_Ioc gaussDensityCore]
  apply Measure.ext_of_Iic
  intro x
  rw [gaussMeasure_Iic_eq_ofReal_gaussCDF,
    MeasureTheory.withDensity_apply _ measurableSet_Iic,
    Measure.restrict_restrict measurableSet_Iic]
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · have hinter : Iic x ∩ Ioc (0 : ℝ) 1 = ∅ := by
      ext y
      simp only [mem_inter_iff, mem_Iic, mem_Ioc, mem_empty_iff_false, iff_false]
      intro hy
      linarith
    rw [hinter, Measure.restrict_empty, lintegral_zero_measure,
      gaussCDF_eq_zero_of_le hx.le, ENNReal.ofReal_zero]
  · have hinter : Iic (0 : ℝ) ∩ Ioc (0 : ℝ) 1 = ∅ := by
      ext y
      simp only [mem_inter_iff, mem_Iic, mem_Ioc, mem_empty_iff_false, iff_false]
      intro hy
      exact (not_lt_of_ge hy.1) hy.2.1
    rw [hinter, Measure.restrict_empty, lintegral_zero_measure,
      gaussCDF_eq_zero_of_le (le_refl 0), ENNReal.ofReal_zero]
  · by_cases hx1 : x < 1
    · have hinter : Iic x ∩ Ioc (0 : ℝ) 1 = Ioc 0 x := by
        ext y
        simp only [mem_inter_iff, mem_Iic, mem_Ioc]
        constructor
        · intro hy
          exact ⟨hy.2.1, hy.1⟩
        · intro hy
          exact ⟨hy.2, hy.1, (hy.2.trans_lt hx1).le⟩
      rw [hinter, lintegral_gaussDensityCore_Ioc (a := 0) (b := x)
        (by norm_num) hx.le hx1.le]
      unfold gaussCDF
      rw [unitClamp_eq_of_mem_Icc ⟨hx.le, hx1.le⟩]
      simp
    · have hx1' : 1 ≤ x := le_of_not_gt hx1
      have hinter : Iic x ∩ Ioc (0 : ℝ) 1 = Ioc 0 1 := by
        ext y
        simp only [mem_inter_iff, mem_Iic, mem_Ioc]
        constructor
        · exact fun hy ↦ hy.2
        · intro hy
          exact ⟨hy.2.trans hx1', hy⟩
      rw [hinter, lintegral_gaussDensityCore_Ioc (a := 0) (b := 1)
        (by norm_num) (by norm_num) (by norm_num), gaussCDF_eq_one_of_le hx1']
      norm_num

theorem gaussDensity_eq_ofReal_on_unit {x : ℝ}
    (hx : x ∈ Ioc (0 : ℝ) 1) :
    gaussDensity x = ENNReal.ofReal (1 / (Real.log 2 * (1 + x))) := by
  simp [gaussDensity, gaussDensityCore, gaussDensityReal, hx]

private theorem gaussDensity_mul_lebesgueOverGaussDensity :
    gaussDensity * lebesgueOverGaussDensity =
      (Ioc (0 : ℝ) 1).indicator 1 := by
  funext x
  by_cases hx : x ∈ Ioc (0 : ℝ) 1
  · simp only [Pi.mul_apply, gaussDensity, indicator_of_mem hx,
      gaussDensityCore, lebesgueOverGaussDensity]
    rw [← ENNReal.ofReal_mul (gaussDensityReal_nonneg_on_unit hx)]
    have hprod :
        gaussDensityReal x * lebesgueOverGaussDensityReal x = 1 := by
      unfold gaussDensityReal lebesgueOverGaussDensityReal
      have hxp : 1 + x ≠ 0 := ne_of_gt (by linarith [hx.1])
      field_simp [hxp]
    rw [hprod]
    simp
  · simp [gaussDensity, hx]

/-- Conversely, weighting Gauss measure by `log 2 * (1+x)` recovers
Lebesgue measure restricted to `(0,1]`.  This is the precise form of
`dLeb / dν_G = log 2 * (1+x)` used in the transfer argument. -/
theorem gaussMeasure_withDensity_lebesgueOverGaussDensity :
    gaussMeasure.withDensity lebesgueOverGaussDensity =
      volume.restrict (Ioc (0 : ℝ) 1) := by
  calc
    gaussMeasure.withDensity lebesgueOverGaussDensity =
        (volume.withDensity gaussDensity).withDensity
          lebesgueOverGaussDensity := by
            rw [gaussMeasure_eq_volume_withDensity]
    _ = volume.withDensity
        (gaussDensity * lebesgueOverGaussDensity) := by
          exact (MeasureTheory.withDensity_mul volume measurable_gaussDensity
            measurable_lebesgueOverGaussDensity).symm
    _ = volume.withDensity ((Ioc (0 : ℝ) 1).indicator 1) := by
          rw [gaussDensity_mul_lebesgueOverGaussDensity]
    _ = volume.restrict (Ioc (0 : ℝ) 1) := by
          exact MeasureTheory.withDensity_indicator_one measurableSet_Ioc

/-- The bounded density used when approximating the Lebesgue-to-Gauss
change of measure by functions measurable with respect to a finite
continued-fraction prefix. -/
def gaussLebesguePrefixWeight (x : ℝ) : ℝ :=
  lebesgueOverGaussDensityReal x

theorem measurable_gaussLebesguePrefixWeight :
    Measurable gaussLebesguePrefixWeight := by
  simpa [gaussLebesguePrefixWeight] using! measurable_lebesgueOverGaussDensityReal

theorem gaussLebesguePrefixWeight_bounds {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) :
    Real.log 2 ≤ gaussLebesguePrefixWeight x ∧
      gaussLebesguePrefixWeight x ≤ 2 * Real.log 2 := by
  simpa [gaussLebesguePrefixWeight] using!
    lebesgueOverGaussDensityReal_bounds hx

end

end Erdos1002
