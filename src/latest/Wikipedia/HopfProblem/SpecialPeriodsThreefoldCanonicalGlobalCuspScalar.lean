import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalCuspScalarRegular
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalCuspScalarUniform

/-!
# The actual regular canonical coefficient near the cusp

The genuine regular coefficient is the source derivative divided by the
constructed global generator.  Its cusp expansion is uniform over all
logarithmic branches and all fibre coordinates.  The imported scalar
germ has a simple pole after division by the exponential parameter, and
the literal reciprocal sphere coordinate cancels that pole to an analytic
nonzero unit.  Comparing this scalar with the native cusp volume remains
the separate genuine derivative-pullback calculation.
-/

noncomputable section

open Filter Topology UpperHalfPlane

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.GlobalCuspScalar

/-- Uniform scalar expansion on every regular lift of every sufficiently
small original cusp parameter. -/
theorem regularCoefficient_uniform : ∀ᶠ q : ℂ in 𝓝 0,
    ∀ z : TriangleRegularPoint, Triangle.cuspQ z.val = q →
      GlobalRegular.regularCoefficient z = coefficientGerm q := by
  filter_upwards [scalarDeriv_div_generator_uniform] with q hq
  intro z hz
  rw [regularCoefficient_eq_scalarDeriv_div_generator]
  exact hq z.val hz

/-- The same actual coefficient formula holds simultaneously on every
point of the original logarithmic cusp cover lying over a small parameter. -/
theorem regularCoefficient_log_uniform : ∀ᶠ q : ℂ in 𝓝 0,
    ∀ x : HolomorphicForms.Cusp.LogDomain, CuspUniformization.exponential x.val.1 = q →
      GlobalRegular.regularCoefficient (HolomorphicForms.Cusp.toRegularCover x).1 =
        coefficientGerm q := by
  filter_upwards [regularCoefficient_uniform] with q hq
  intro x hx
  exact hq _ ((cuspQ_toRegularCover x).trans hx)

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.GlobalCuspScalar
