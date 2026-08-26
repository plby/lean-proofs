import ErdosProblems.Erdos1002.ProbabilityFoundations

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# From weak convergence to the Erdős 1002 distributional conclusion

This file isolates the final Portmanteau step.  Weak convergence of the laws
of the normalized rotation sums to the centered Cauchy law implies convergence
of their distribution functions at every real threshold.  The only
continuity-set input is that the limiting Stieltjes measure has no atoms.
-/

open Filter MeasureTheory Set
open scoped Topology ENNReal

namespace Erdos1002

noncomputable section

theorem continuous_cauchyLimitCDF : Continuous cauchyLimitCDF := by
  unfold cauchyLimitCDF
  fun_prop

theorem cauchyLimitMeasure_singleton (c : ℝ) :
    cauchyLimitMeasure {c} = 0 := by
  rw [cauchyLimitMeasure, StieltjesFunction.measure_singleton]
  have hcontinuous : Continuous (↑cauchyLimitStieltjes : ℝ → ℝ) := by
    change Continuous cauchyLimitCDF
    exact continuous_cauchyLimitCDF
  rw [hcontinuous.continuousAt.continuousWithinAt.leftLim_eq]
  simp

theorem cauchyLimitProbability_Iic_isContinuitySet (c : ℝ) :
    (cauchyLimitProbability : Measure ℝ) (frontier (Iic c)) = 0 := by
  rw [frontier_Iic]
  exact cauchyLimitMeasure_singleton c

/-- The exact CDF conclusion in the manuscript follows from weak convergence
of the normalized rotation-sum laws to the centered Cauchy probability law. -/
theorem erdos1002Conclusion_of_rotationLaw_tendsto
    (hweak : Tendsto rotationLaw atTop (nhds cauchyLimitProbability)) :
    Erdos1002Conclusion := by
  intro c
  have hmeasure :=
    ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto'
      hweak (cauchyLimitProbability_Iic_isContinuitySet c)
  have hreal :
      Tendsto
        (fun N : ℕ ↦ ((rotationLaw N : Measure ℝ) (Iic c)).toReal)
        atTop
        (nhds (((cauchyLimitProbability : Measure ℝ) (Iic c)).toReal)) :=
    (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp hmeasure
  have hcdf :
      Tendsto
        (fun N : ℕ ↦ ProbabilityTheory.cdf (rotationLaw N : Measure ℝ) c)
        atTop
        (nhds (ProbabilityTheory.cdf cauchyLimitMeasure c)) := by
    simpa only [ProbabilityTheory.cdf_eq_real, cauchyLimitProbability] using! hreal
  simpa only [
    cdf_rotationLaw_eq_distributionValue,
    cdf_cauchyLimitMeasure_apply] using! hcdf

end

end Erdos1002
