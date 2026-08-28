import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalCuspScalarBasic
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldHolomorphicFormsCuspComparisonBase

/-!
# Uniform cusp scalar identities on all logarithmic branches

The exact norm formula for the original cusp exponential identifies
small punctured parameter discs with high horodiscs.  Consequently an
eventual statement at imaginary infinity holds uniformly for every lift
of each sufficiently small parameter, not merely on one logarithm branch.
-/

noncomputable section

open Set Filter Topology UpperHalfPlane

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.GlobalCuspScalar

open Triangle TriangleHolomorphicDifferentials

/-- An eventual property at imaginary infinity holds on all lifts of
every sufficiently small actual cusp parameter. -/
theorem eventually_all_cuspQ_lifts {P : ℍ → Prop} (hP : ∀ᶠ z in atImInfty, P z) :
    ∀ᶠ q : ℂ in 𝓝 0, ∀ z : ℍ, cuspQ z = q → P z := by
  obtain ⟨Y, hY⟩ := (UpperHalfPlane.atImInfty_mem _).mp hP
  filter_upwards [Metric.ball_mem_nhds (0 : ℂ)
    (Real.exp_pos (-2 * Real.pi * Y / width))] with q hq
  intro z hz
  have hn : ‖cuspQ z‖ < Real.exp (-2 * Real.pi * Y / width) := by
    simpa only [hz, Metric.mem_ball, dist_zero_right] using hq
  exact hY z ((cuspQ_norm_lt_exp_iff Y z).mp hn).le

/-- The actual scalar formula is uniform on the entire fibre of the
cusp exponential over every sufficiently small parameter. -/
theorem scalarDeriv_div_generator_uniform : ∀ᶠ q : ℂ in 𝓝 0,
    ∀ z : ℍ, cuspQ z = q →
      scalarDeriv specialSourceCoordinate z / GlobalGenerator.generator z =
        coefficientGerm q := by
  filter_upwards [eventually_all_cuspQ_lifts scalarDeriv_div_generator_eventually] with q hq
  intro z hz
  simpa only [hz] using hq z hz

/-- The actual width-scaled comparison has exactly the original cusp parameter. -/
theorem cuspQ_toRegularCover (x : HolomorphicForms.Cusp.LogDomain) :
    cuspQ (HolomorphicForms.Cusp.toRegularCover x).1.val =
      CuspUniformization.exponential x.val.1 :=
  CuspFamily.logBaseToRegular_cuspQ CuspGeometry.data.radius
    HolomorphicForms.Cusp.radius_cap (HolomorphicForms.Cusp.toLogBase x)

/-- Uniformity on every point of the actual logarithmic cover, including
every logarithm branch and every pair of fibre coordinates. -/
theorem scalarDeriv_div_generator_log_uniform : ∀ᶠ q : ℂ in 𝓝 0,
    ∀ x : HolomorphicForms.Cusp.LogDomain, CuspUniformization.exponential x.val.1 = q →
      scalarDeriv specialSourceCoordinate (HolomorphicForms.Cusp.toRegularCover x).1.val /
          GlobalGenerator.generator (HolomorphicForms.Cusp.toRegularCover x).1.val =
        coefficientGerm q := by
  filter_upwards [scalarDeriv_div_generator_uniform] with q hq
  intro x hx
  exact hq _ ((cuspQ_toRegularCover x).trans hx)

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.GlobalCuspScalar
