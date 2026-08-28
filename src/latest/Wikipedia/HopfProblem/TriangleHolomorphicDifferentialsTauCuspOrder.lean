import Wikipedia.HopfProblem.TriangleHolomorphicDifferentialsTauCusp
import Wikipedia.HopfProblem.TriangleHolomorphicDifferentialsGeometry
import Wikipedia.HopfProblem.TriangleHolomorphicDifferentialsCuspOrder

/-!
# The analytic cusp order of the first period's scalar derivative

The actual logarithmic cusp expansion gives an analytic germ for the scalar
derivative of `specialTau`.  Thus it has cusp order zero, with leading value
`1 / width`.
-/

noncomputable section

open Filter Set Topology UpperHalfPlane
open scoped ContDiff

namespace Wikipedia.HopfProblem.TriangleHolomorphicDifferentials

open SpecialPeriods SpecialPeriods.Triangle

/-- The derivative formula in the named scalar-derivative convention. -/
theorem specialTau_scalarDeriv_cusp (z : ℍ)
    (hz : ‖cuspQ z‖ < specialCuspData.radius) :
    scalarDeriv specialTau z = 1 / (width : ℂ) +
      deriv specialCuspData.h (cuspQ z) *
        ((2 * Real.pi * Complex.I / (width : ℂ)) * cuspQ z) :=
  specialTau_deriv_cusp z hz

/-- The constructed correction term is genuinely analytic at the cusp. -/
theorem specialCuspData_h_analyticAt_zero : AnalyticAt ℂ specialCuspData.h 0 :=
  (specialCuspData_h_holomorphic.contDiffAt
    (Metric.ball_mem_nhds (0 : ℂ) specialCuspData.radius_pos)).analyticAt

/-- The first period's derivative has analytic cusp order zero. -/
theorem specialTau_scalarDeriv_hasCuspOrder_zero :
    HasCuspOrder 0 (scalarDeriv specialTau) := by
  refine ⟨fun q => 1 / (width : ℂ) + deriv specialCuspData.h q *
    ((2 * Real.pi * Complex.I / (width : ℂ)) * q), ?_, ?_⟩
  · exact analyticAt_const.add (specialCuspData_h_analyticAt_zero.deriv.mul
      (analyticAt_const.mul analyticAt_id))
  · have hsmall : ∀ᶠ z in atImInfty, ‖cuspQ z‖ < specialCuspData.radius := by
      have hq := cuspQ_tendsto_atImInfty.mono_right nhdsWithin_le_nhds
      simpa only [Metric.mem_ball, dist_zero_right] using
        hq.eventually (Metric.ball_mem_nhds (0 : ℂ) specialCuspData.radius_pos)
    filter_upwards [hsmall] with z hz
    simpa only [pow_zero, one_mul] using specialTau_scalarDeriv_cusp z hz

end Wikipedia.HopfProblem.TriangleHolomorphicDifferentials
