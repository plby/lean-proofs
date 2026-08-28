import Wikipedia.HopfProblem.SpecialPeriodsModularLocalCharts
import Wikipedia.HopfProblem.SpecialPeriodsModularRamification

/-!
# Local branched-cover charts for the actual modular function

The charts constructed here are genuine open partial homeomorphisms with
holomorphic forward and inverse maps.  Their source is contained in the upper
half-plane.  At each point over zero the actual modular function is a cube;
at each point over 1728 its difference from 1728 is a square.  The assertions
include the inverse-chart identities on the whole target neighborhood.
-/

noncomputable section

open Set UpperHalfPlane
open scoped Topology

namespace Wikipedia.HopfProblem.SpecialPeriods

/-- A cubic local branched-cover chart at every point over `j = 0`. -/
theorem modularJ_cubic_chart (z : ℍ) (hz : modularJ z = 0) :
    ∃ e : OpenPartialHomeomorph ℂ ℂ,
      (z : ℂ) ∈ e.source ∧ e z = 0 ∧ e.source ⊆ upperHalfPlaneSet ∧
      AnalyticOnNhd ℂ e e.source ∧ AnalyticOnNhd ℂ e.symm e.target ∧
      (∀ w ∈ e.source, modularJ (ofComplex w) = e w ^ 3) ∧
      (∀ w ∈ e.target, modularJ (ofComplex (e.symm w)) = w ^ 3) := by
  obtain ⟨e, ha, he, hU, hf, hi, hp⟩ := exists_analytic_power_chart_in
    (modularJ_analyticAt z) (analyticOrderAt_modularJ_of_eq_zero z hz)
    (by decide : 0 < 3) (isOpen_upperHalfPlaneSet.mem_nhds z.im_pos)
  exact ⟨e, ha, he, hU, hf, hi, hp, power_chart_inverse_identity e hp⟩

/-- A quadratic local branched-cover chart at every point over `j = 1728`. -/
theorem modularJ_quadratic_chart (z : ℍ) (hz : modularJ z = 1728) :
    ∃ e : OpenPartialHomeomorph ℂ ℂ,
      (z : ℂ) ∈ e.source ∧ e z = 0 ∧ e.source ⊆ upperHalfPlaneSet ∧
      AnalyticOnNhd ℂ e e.source ∧ AnalyticOnNhd ℂ e.symm e.target ∧
      (∀ w ∈ e.source, modularJ (ofComplex w) - 1728 = e w ^ 2) ∧
      (∀ w ∈ e.target, modularJ (ofComplex (e.symm w)) - 1728 = w ^ 2) := by
  obtain ⟨e, ha, he, hU, hf, hi, hp⟩ := exists_analytic_power_chart_in
    ((modularJ_analyticAt z).sub analyticAt_const)
    (analyticOrderAt_modularJ_sub_1728_of_eq z hz)
    (by decide : 0 < 2) (isOpen_upperHalfPlaneSet.mem_nhds z.im_pos)
  exact ⟨e, ha, he, hU, hf, hi, hp, power_chart_inverse_identity e hp⟩

/-- At regular points, the shifted modular function itself is a
biholomorphic coordinate on an actual open neighborhood. -/
theorem modularJ_regular_chart (z : ℍ)
    (h₀ : modularJ z ≠ 0) (h₁ : modularJ z ≠ 1728) :
    ∃ e : OpenPartialHomeomorph ℂ ℂ,
      (z : ℂ) ∈ e.source ∧ e z = 0 ∧ e.source ⊆ upperHalfPlaneSet ∧
      AnalyticOnNhd ℂ e e.source ∧ AnalyticOnNhd ℂ e.symm e.target ∧
      (∀ w ∈ e.source, modularJ (ofComplex w) - modularJ z = e w) ∧
      (∀ w ∈ e.target, modularJ (ofComplex (e.symm w)) - modularJ z = w) := by
  obtain ⟨e, ha, he, hU, hf, hi, hp⟩ := exists_analytic_power_chart_in
    ((modularJ_analyticAt z).sub analyticAt_const)
    (analyticOrderAt_modularJ_sub_value_of_regular z h₀ h₁)
    (by decide : 0 < 1) (isOpen_upperHalfPlaneSet.mem_nhds z.im_pos)
  refine ⟨e, ha, he, hU, hf, hi, ?_, ?_⟩
  · simpa only [pow_one, Pi.sub_apply, Function.comp_apply] using hp
  · simpa only [pow_one, Pi.sub_apply, Function.comp_apply] using
      power_chart_inverse_identity e hp

/-- The distinguished cubic chart at the paper's elliptic point `ρ`. -/
theorem modularJ_rhoPoint_cubic_chart :
    ∃ e : OpenPartialHomeomorph ℂ ℂ,
      rho ∈ e.source ∧ e rho = 0 ∧ e.source ⊆ upperHalfPlaneSet ∧
      AnalyticOnNhd ℂ e e.source ∧ AnalyticOnNhd ℂ e.symm e.target ∧
      (∀ w ∈ e.source, modularJ (ofComplex w) = e w ^ 3) ∧
      (∀ w ∈ e.target, modularJ (ofComplex (e.symm w)) = w ^ 3) :=
  modularJ_cubic_chart rhoPoint modularJ_rhoPoint

/-- The distinguished quadratic chart at `i`. -/
theorem modularJ_I_quadratic_chart :
    ∃ e : OpenPartialHomeomorph ℂ ℂ,
      Complex.I ∈ e.source ∧ e Complex.I = 0 ∧ e.source ⊆ upperHalfPlaneSet ∧
      AnalyticOnNhd ℂ e e.source ∧ AnalyticOnNhd ℂ e.symm e.target ∧
      (∀ w ∈ e.source, modularJ (ofComplex w) - 1728 = e w ^ 2) ∧
      (∀ w ∈ e.target, modularJ (ofComplex (e.symm w)) - 1728 = w ^ 2) :=
  modularJ_quadratic_chart UpperHalfPlane.I modularJ_I

end Wikipedia.HopfProblem.SpecialPeriods
