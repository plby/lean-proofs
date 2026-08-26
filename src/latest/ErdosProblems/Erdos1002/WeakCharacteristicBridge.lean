import ErdosProblems.Erdos1002.CauchyAnalysis
import ErdosProblems.Erdos1002.ConvergenceBridge
import ErdosProblems.Erdos1002.LevyContinuity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Characteristic-function criterion for the Erdős 1002 laws

This file records the exact probability-theoretic interface needed by the
remaining arithmetic argument.  Weak convergence of the normalized
rotation-sum laws to the limiting Cauchy law is equivalent to pointwise
convergence of their characteristic functions to the exact Cauchy
characteristic function.  Consequently, this pointwise convergence implies
the distribution-function conclusion in `Erdos1002Conclusion`.
-/

open Filter MeasureTheory
open scoped Topology

namespace Erdos1002

noncomputable section

/-- Weak convergence of the normalized rotation-sum laws to the limiting
Cauchy law is equivalent to pointwise convergence of their characteristic
functions to `exp (-|t| / (2π))`.

The forward implication is the defining bounded-continuous-test-function
property of weak convergence.  The reverse implication is Lévy's continuity
theorem on `ℝ`, proved in `LevyContinuity`. -/
theorem rotationLaw_tendsto_cauchyLimitProbability_iff_charFun :
    Tendsto rotationLaw atTop (nhds cauchyLimitProbability) ↔
      ∀ t : ℝ,
        Tendsto
          (fun N : ℕ ↦ charFun (rotationLaw N : Measure ℝ) t)
          atTop
          (nhds (Complex.exp (-(|t| / (2 * Real.pi) : ℝ)))) := by
  constructor
  · intro hweak t
    have hchar :=
      (ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ).mp
        hweak (BoundedContinuousFunction.innerProbChar t)
    have hchar' :
        Tendsto
          (fun N : ℕ ↦ charFun (rotationLaw N : Measure ℝ) t)
          atTop
          (nhds (charFun (cauchyLimitProbability : Measure ℝ) t)) := by
      simpa only [charFun_eq_integral_innerProbChar] using! hchar
    simpa only [charFun_cauchyLimitProbability] using! hchar'
  · intro hchar
    apply levy_continuity_real rotationLaw cauchyLimitProbability
    intro t
    simpa only [charFun_cauchyLimitProbability] using! hchar t

/-- Pointwise convergence of the normalized rotation-sum characteristic
functions to the exact Cauchy characteristic function implies the original
Erdős 1002 distributional conclusion. -/
theorem erdos1002Conclusion_of_rotationLaw_charFun_tendsto
    (hchar : ∀ t : ℝ,
      Tendsto
        (fun N : ℕ ↦ charFun (rotationLaw N : Measure ℝ) t)
        atTop
        (nhds (Complex.exp (-(|t| / (2 * Real.pi) : ℝ))))) :
    Erdos1002Conclusion := by
  apply erdos1002Conclusion_of_rotationLaw_tendsto
  exact rotationLaw_tendsto_cauchyLimitProbability_iff_charFun.mpr hchar

end

end Erdos1002
