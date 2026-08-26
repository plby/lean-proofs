import ErdosProblems.Erdos1002.GaussMeasure
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Asymptotics of one-digit Gauss cylinders

The marked Poisson argument needs the leading constant in the rare event
`a₁ ≍ L`.  This file derives it from the exact cylinder formula, with an
ordinary sequential limit rather than an informal Taylor expansion.
-/

open Filter MeasureTheory
open scoped Topology

namespace Erdos1002

noncomputable section

private def shiftedDigit (n : ℕ) : ℕ := n + 1

private def shiftedDigitReal (n : ℕ) : ℝ := (shiftedDigit n : ℝ)

private def digitScale (n : ℕ) : ℝ :=
  shiftedDigitReal n * (shiftedDigitReal n + 2)

private theorem tendsto_shiftedDigitReal_atTop :
    Tendsto shiftedDigitReal atTop atTop := by
  unfold shiftedDigitReal shiftedDigit
  exact tendsto_natCast_atTop_atTop.comp (Filter.tendsto_add_atTop_nat 1)

private theorem tendsto_digitScale_atTop : Tendsto digitScale atTop atTop := by
  have hq := tendsto_shiftedDigitReal_atTop
  have hq2 : Tendsto (fun n ↦ shiftedDigitReal n + 2) atTop atTop :=
    Filter.tendsto_atTop_mono (fun n ↦ by linarith)
      tendsto_shiftedDigitReal_atTop
  exact hq.atTop_mul_atTop₀ hq2

private theorem digit_ratio_identity (n : ℕ) :
    ((shiftedDigit n : ℝ) + 1) ^ 2 /
        ((shiftedDigit n : ℝ) * ((shiftedDigit n : ℝ) + 2)) =
      1 + 1 / digitScale n := by
  have hq : (shiftedDigit n : ℝ) ≠ 0 := by
    unfold shiftedDigit
    positivity
  have hq2 : (shiftedDigit n : ℝ) + 2 ≠ 0 := by positivity
  unfold digitScale shiftedDigitReal
  field_simp
  ring

private theorem tendsto_digitScale_mul_log :
    Tendsto
      (fun n ↦ digitScale n * Real.log (1 + 1 / digitScale n))
      atTop (nhds 1) := by
  simpa only [one_div] using!
    (Real.tendsto_mul_log_one_add_div_atTop 1).comp tendsto_digitScale_atTop

private theorem shiftedDigit_sq_div_digitScale (n : ℕ) :
    shiftedDigitReal n ^ 2 / digitScale n =
      1 - 2 / (shiftedDigitReal n + 2) := by
  have hq : shiftedDigitReal n ≠ 0 := by
    unfold shiftedDigitReal shiftedDigit
    positivity
  have hq2 : shiftedDigitReal n + 2 ≠ 0 := by
    unfold shiftedDigitReal shiftedDigit
    positivity
  unfold digitScale
  field_simp
  ring

private theorem tendsto_shiftedDigit_sq_div_digitScale :
    Tendsto (fun n ↦ shiftedDigitReal n ^ 2 / digitScale n)
      atTop (nhds 1) := by
  have hq2 : Tendsto (fun n ↦ shiftedDigitReal n + 2) atTop atTop :=
    Filter.tendsto_atTop_mono (fun n ↦ by linarith)
      tendsto_shiftedDigitReal_atTop
  have hdiv : Tendsto (fun n ↦ 2 / (shiftedDigitReal n + 2))
      atTop (nhds 0) := hq2.const_div_atTop 2
  have hsub : Tendsto (fun n ↦ 1 - 2 / (shiftedDigitReal n + 2))
      atTop (nhds 1) := by
    simpa only [sub_zero] using! tendsto_const_nhds.sub hdiv
  exact hsub.congr' (Eventually.of_forall fun n ↦
    (shiftedDigit_sq_div_digitScale n).symm)

private theorem digit_mass_scaled_identity (n : ℕ) :
    shiftedDigitReal n ^ 2 *
        gaussMeasure.real (firstDigitCylinder (shiftedDigit n)) =
      (shiftedDigitReal n ^ 2 / digitScale n) *
        (digitScale n * Real.log (1 + 1 / digitScale n)) /
          Real.log 2 := by
  have hq : 0 < shiftedDigit n := by
    unfold shiftedDigit
    omega
  rw [gaussMeasure_real_firstDigitCylinder (shiftedDigit n) hq]
  have hratio :
      (((shiftedDigit n + 1 : ℕ) : ℝ) ^ 2 /
        ((shiftedDigit n : ℝ) * (shiftedDigit n + 2 : ℕ))) =
        1 + 1 / digitScale n := by
    norm_num [Nat.cast_add]
    simpa only [one_div] using! digit_ratio_identity n
  rw [hratio]
  have hscale : digitScale n ≠ 0 := by
    unfold digitScale shiftedDigitReal shiftedDigit
    positivity
  unfold shiftedDigitReal
  field_simp

/-- Exact leading constant in the one-digit rare-event probability:
`q² ν_G(a₁=q) →1/log 2`. -/
theorem tendsto_gauss_firstDigitCylinder_scaled :
    Tendsto
      (fun n : ℕ ↦ shiftedDigitReal n ^ 2 *
        gaussMeasure.real (firstDigitCylinder (shiftedDigit n)))
      atTop (nhds (1 / Real.log 2)) := by
  have hprod := tendsto_shiftedDigit_sq_div_digitScale.mul
    tendsto_digitScale_mul_log
  have hdiv := hprod.div_const (Real.log 2)
  simpa only [one_mul] using! hdiv.congr'
    (Eventually.of_forall fun n ↦ (digit_mass_scaled_identity n).symm)

/-- Exact Gauss mass of the large-first-digit tail.  In regular continued
fractions the condition `a₁ ≥ q` is the interval `(0,1/q]`. -/
theorem gaussMeasure_real_firstDigitTail (q : ℕ) (hq : 0 < q) :
    gaussMeasure.real (Set.Ioc (0 : ℝ) (1 / (q : ℝ))) =
      Real.log (1 + 1 / (q : ℝ)) / Real.log 2 := by
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  simpa using! gaussMeasure_real_Ioc
    (a := (0 : ℝ)) (b := 1 / (q : ℝ))
    (by norm_num) (by positivity) (by
      rw [div_le_one hqR]
      exact_mod_cast hq)

private theorem firstDigitTail_scaled_identity (n : ℕ) :
    shiftedDigitReal n *
        gaussMeasure.real
          (Set.Ioc (0 : ℝ) (1 / (shiftedDigit n : ℝ))) =
      (shiftedDigitReal n *
          Real.log (1 + 1 / shiftedDigitReal n)) / Real.log 2 := by
  have hq : 0 < shiftedDigit n := by
    unfold shiftedDigit
    omega
  rw [gaussMeasure_real_firstDigitTail (shiftedDigit n) hq]
  unfold shiftedDigitReal
  ring

/-- The exact rare-event constant for large first continued-fraction digits:
`q ν_G(a₁ ≥ q) → 1 / log 2`. -/
theorem tendsto_gauss_firstDigitTail_scaled :
    Tendsto
      (fun n : ℕ ↦ shiftedDigitReal n *
        gaussMeasure.real
          (Set.Ioc (0 : ℝ) (1 / (shiftedDigit n : ℝ))))
      atTop (nhds (1 / Real.log 2)) := by
  have hcore : Tendsto
      (fun n : ℕ ↦ shiftedDigitReal n *
        Real.log (1 + 1 / shiftedDigitReal n))
      atTop (nhds 1) := by
    simpa only [one_div] using!
      (Real.tendsto_mul_log_one_add_div_atTop 1).comp
        tendsto_shiftedDigitReal_atTop
  have hdiv := hcore.div_const (Real.log 2)
  exact hdiv.congr' (Eventually.of_forall fun n ↦
    (firstDigitTail_scaled_identity n).symm)

end

end Erdos1002
