import ErdosProblems.Erdos1002.FiniteFacts

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Probability foundations for Erdős Problem 1002

This file packages the Lebesgue distribution functions in the statement as
probability measures.  It also constructs the limiting centered Cauchy law
directly from its distribution function, so later convergence arguments can
use mathlib's weak-convergence API without changing the theorem being proved.
-/

open Filter MeasureTheory Set
open scoped BigOperators Topology

namespace Erdos1002

noncomputable section

/-- Lebesgue measure restricted to the open unit interval. -/
def uniform01Measure : Measure ℝ :=
  volume.restrict (Ioo (0 : ℝ) 1)

instance uniform01Measure_isProbabilityMeasure :
    IsProbabilityMeasure uniform01Measure where
  measure_univ := by
    simp [uniform01Measure]

/-- Uniform probability measure on the open unit interval. -/
def uniform01 : ProbabilityMeasure ℝ :=
  ⟨uniform01Measure, inferInstance⟩

/-- The law of the normalized rotation sum under uniform Lebesgue measure. -/
def rotationLaw (N : ℕ) : ProbabilityMeasure ℝ :=
  uniform01.map (measurable_normalizedRotationSum N).aemeasurable

theorem cdf_rotationLaw_eq_distributionValue (N : ℕ) (c : ℝ) :
    ProbabilityTheory.cdf (rotationLaw N : Measure ℝ) c =
      distributionValue N c := by
  rw [ProbabilityTheory.cdf_eq_real]
  change ((uniform01Measure.map (normalizedRotationSum N)).real (Iic c)) = _
  rw [map_measureReal_apply
    (measurable_normalizedRotationSum N) measurableSet_Iic]
  rw [show uniform01Measure = volume.restrict (Ioo (0 : ℝ) 1) from rfl]
  rw [measureReal_restrict_apply' measurableSet_Ioo]
  unfold distributionValue
  congr 1
  ext α
  simp [and_comm]

/-- The Stieltjes function of the centered Cauchy law of scale `1 / (2π)`. -/
def cauchyLimitStieltjes : StieltjesFunction ℝ where
  toFun := cauchyLimitCDF
  mono' := by
    intro a b hab
    unfold cauchyLimitCDF
    gcongr
  right_continuous' := by
    intro x
    apply Continuous.continuousWithinAt
    unfold cauchyLimitCDF
    fun_prop

theorem tendsto_cauchyLimitCDF_atTop :
    Tendsto cauchyLimitCDF atTop (nhds 1) := by
  have harg : Tendsto (fun c : ℝ ↦ (2 * Real.pi) * c) atTop atTop :=
    tendsto_id.const_mul_atTop (mul_pos (by positivity) Real.pi_pos)
  have hatan :
      Tendsto (fun c : ℝ ↦ Real.arctan ((2 * Real.pi) * c)) atTop
        (nhds (Real.pi / 2)) :=
    (tendsto_nhds_of_tendsto_nhdsWithin Real.tendsto_arctan_atTop).comp harg
  have hscaled :
      Tendsto (fun c : ℝ ↦ (1 / Real.pi) * Real.arctan ((2 * Real.pi) * c))
        atTop (nhds ((1 / Real.pi) * (Real.pi / 2))) :=
    hatan.const_mul (1 / Real.pi)
  have h := hscaled.const_add ((1 : ℝ) / 2)
  have hend :
      (1 : ℝ) / 2 + (1 / Real.pi) * (Real.pi / 2) = 1 := by
    field_simp [Real.pi_ne_zero]
    norm_num
  simpa only [cauchyLimitCDF, hend] using! h

theorem tendsto_cauchyLimitCDF_atBot :
    Tendsto cauchyLimitCDF atBot (nhds 0) := by
  have harg : Tendsto (fun c : ℝ ↦ (2 * Real.pi) * c) atBot atBot :=
    tendsto_id.const_mul_atBot (mul_pos (by positivity) Real.pi_pos)
  have hatan :
      Tendsto (fun c : ℝ ↦ Real.arctan ((2 * Real.pi) * c)) atBot
        (nhds (-(Real.pi / 2))) :=
    (tendsto_nhds_of_tendsto_nhdsWithin Real.tendsto_arctan_atBot).comp harg
  have hscaled :
      Tendsto (fun c : ℝ ↦ (1 / Real.pi) * Real.arctan ((2 * Real.pi) * c))
        atBot (nhds ((1 / Real.pi) * (-(Real.pi / 2)))) :=
    hatan.const_mul (1 / Real.pi)
  have h := hscaled.const_add ((1 : ℝ) / 2)
  have hend :
      (1 : ℝ) / 2 + (1 / Real.pi) * (-(Real.pi / 2)) = 0 := by
    field_simp [Real.pi_ne_zero]
    norm_num
  simpa only [cauchyLimitCDF, hend] using! h

/-- The centered Cauchy measure whose CDF is `cauchyLimitCDF`. -/
def cauchyLimitMeasure : Measure ℝ :=
  cauchyLimitStieltjes.measure

instance cauchyLimitMeasure_isProbabilityMeasure :
    IsProbabilityMeasure cauchyLimitMeasure := by
  refine ⟨?_⟩
  simpa [cauchyLimitMeasure] using!
    (cauchyLimitStieltjes.measure_univ tendsto_cauchyLimitCDF_atBot
      tendsto_cauchyLimitCDF_atTop)

/-- The limiting centered Cauchy probability measure. -/
def cauchyLimitProbability : ProbabilityMeasure ℝ :=
  ⟨cauchyLimitMeasure, inferInstance⟩

theorem cdf_cauchyLimitMeasure :
    ProbabilityTheory.cdf cauchyLimitMeasure = cauchyLimitStieltjes := by
  exact ProbabilityTheory.cdf_measure_stieltjesFunction cauchyLimitStieltjes
    tendsto_cauchyLimitCDF_atBot tendsto_cauchyLimitCDF_atTop

theorem cdf_cauchyLimitMeasure_apply (c : ℝ) :
    ProbabilityTheory.cdf cauchyLimitMeasure c = cauchyLimitCDF c := by
  rw [cdf_cauchyLimitMeasure]
  rfl

end

end Erdos1002
