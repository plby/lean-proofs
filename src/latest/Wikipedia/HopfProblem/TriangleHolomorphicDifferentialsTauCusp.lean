import Wikipedia.HopfProblem.SpecialPeriodsExistence

/-!
# The derivative of the actual first period at the cusp

The proved logarithmic cusp expansion of `specialTau` differentiates in the
ordinary upper-half-plane coordinate.  The holomorphy of its correction term
is extracted from the actual cusp data, not supplied as another hypothesis.
-/

noncomputable section

open Filter Set UpperHalfPlane
open scoped Topology ContDiff

namespace Wikipedia.HopfProblem.TriangleHolomorphicDifferentials

open SpecialPeriods SpecialPeriods.Triangle

/-- The first entry of the actual period-point cusp expansion. -/
theorem specialTau_eq_cuspExpansion (z : ℍ)
    (hz : ‖cuspQ z‖ < specialCuspData.radius) :
    specialTau z = (z : ℂ) / width + specialCuspData.h (cuspQ z) := by
  have h := congrArg PeriodPoint.τ (specialCuspData_periodPoint z hz)
  simpa only [specialTau, cuspPeriodPoint,
    Construction.exponential_normalized_eq_cuspQ] using h

/-- The cusp correction in the first period is holomorphic on the actual
positive-radius disc already constructed with the cusp family. -/
theorem specialCuspData_h_holomorphic :
    ContDiffOn ℂ ω specialCuspData.h (Metric.ball 0 specialCuspData.radius) :=
  specialCuspData.holomorphic 0 1

/-- Differentiating the actual cusp expansion, with no additional analytic
assumption on its correction term. -/
theorem specialTau_hasDerivAt_cusp (z : ℍ)
    (hz : ‖cuspQ z‖ < specialCuspData.radius) :
    HasDerivAt (specialTau ∘ UpperHalfPlane.ofComplex)
      (1 / (width : ℂ) + deriv specialCuspData.h (cuspQ z) *
        ((2 * Real.pi * Complex.I / (width : ℂ)) * cuspQ z)) (z : ℂ) := by
  have hh : DifferentiableAt ℂ specialCuspData.h (cuspQ z) :=
    (specialCuspData_h_holomorphic.contDiffAt
      (Metric.isOpen_ball.mem_nhds (by simpa using hz))).differentiableAt (by simp)
  have hq := (cuspQ_hasStrictDerivAt z).hasDerivAt
  have hh' : HasDerivAt specialCuspData.h (deriv specialCuspData.h (cuspQ z))
      ((cuspQ ∘ UpperHalfPlane.ofComplex) (z : ℂ)) := by
    simpa only [Function.comp_apply, UpperHalfPlane.ofComplex_apply] using hh.hasDerivAt
  have hsum := ((hasDerivAt_id (z : ℂ)).div_const (width : ℂ)).add
    (hh'.comp (z : ℂ) hq)
  have heq : specialTau ∘ UpperHalfPlane.ofComplex =ᶠ[𝓝 (z : ℂ)]
      fun w => w / (width : ℂ) + specialCuspData.h (cuspQ (UpperHalfPlane.ofComplex w)) := by
    have hsmall : ∀ᶠ w in 𝓝 (z : ℂ),
        ‖cuspQ (UpperHalfPlane.ofComplex w)‖ < specialCuspData.radius :=
      hq.continuousAt.norm.eventually_lt_const (by simpa using hz)
    filter_upwards [hsmall, UpperHalfPlane.eventuallyEq_coe_comp_ofComplex z.im_pos]
      with w hw hcoe
    rw [Function.comp_apply, specialTau_eq_cuspExpansion _ hw]
    exact congrArg (fun t : ℂ => t / width +
      specialCuspData.h (cuspQ (UpperHalfPlane.ofComplex w))) hcoe
  simpa only [mul_comm] using hsum.congr_of_eventuallyEq heq

/-- The scalar complex derivative of the actual first period in the cusp
coordinate, with its exact logarithmic leading term. -/
theorem specialTau_deriv_cusp (z : ℍ)
    (hz : ‖cuspQ z‖ < specialCuspData.radius) :
    deriv (specialTau ∘ UpperHalfPlane.ofComplex) (z : ℂ) =
      1 / (width : ℂ) + deriv specialCuspData.h (cuspQ z) *
        ((2 * Real.pi * Complex.I / (width : ℂ)) * cuspQ z) :=
  (specialTau_hasDerivAt_cusp z hz).deriv

end Wikipedia.HopfProblem.TriangleHolomorphicDifferentials
