import Wikipedia.HopfProblem.TriangleHolomorphicDifferentialsCuspCoordinatesDerivative
import Wikipedia.HopfProblem.TriangleHolomorphicDifferentialsCuspCoordinatesAlgebra
import Wikipedia.HopfProblem.SpecialPeriodsExistence

/-!
# Vanishing coefficient germs for the actual source uniformization

The normalized source coordinate is the one supplied by the constructed
triangle-sphere biholomorphism.  Its reciprocal coordinate has a simple
zero in the actual exponential cusp parameter, and both required units
come from that proved local biholomorphism.  The first- and third-degree
normalized coefficients therefore have actual analytic cusp germs that
vanish at zero.  No coordinate, unit, or derivative formula is assumed.
-/

noncomputable section

open Set Filter Topology UpperHalfPlane
open scoped ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.TriangleHolomorphicDifferentials

open SpecialPeriods SpecialPeriods.Triangle

attribute [local instance] triangleCompactifiedChartedSpace

/-- The actual reciprocal sphere coordinate in the source exponential cusp chart. -/
def specialCuspCoordinate : ℂ → ℂ :=
  MuTorsor.CuspCoordinates.t triangleSphereUniformization

/-- The canonical divided slope of the actual reciprocal cusp coordinate. -/
def specialCuspUnit : ℂ → ℂ :=
  MuTorsor.CuspCoordinates.tDivQ triangleSphereUniformization

theorem specialCuspCoordinate_analyticAt_zero : AnalyticAt ℂ specialCuspCoordinate 0 :=
  MuTorsor.CuspCoordinates.t_analyticAt_zero triangleSphereUniformization
    triangleSphereUniformization_cusp

@[simp] theorem specialCuspCoordinate_zero : specialCuspCoordinate 0 = 0 :=
  MuTorsor.CuspCoordinates.t_zero triangleSphereUniformization triangleSphereUniformization_cusp

theorem specialCuspCoordinate_deriv_analyticAt_zero :
    AnalyticAt ℂ (deriv specialCuspCoordinate) 0 :=
  specialCuspCoordinate_analyticAt_zero.deriv

/-- Nonvanishing follows from the actual cusp chart and the actual sphere biholomorphism. -/
theorem specialCuspCoordinate_deriv_ne_zero : deriv specialCuspCoordinate 0 ≠ 0 :=
  TriangleSource.reciprocalCusp_deriv_ne_zero triangleSphereUniformization
    triangleSphereUniformization_cusp

theorem specialCuspUnit_analyticAt_zero : AnalyticAt ℂ specialCuspUnit 0 :=
  MuTorsor.CuspCoordinates.tDivQ_analyticAt_zero triangleSphereUniformization
    triangleSphereUniformization_cusp

theorem specialCuspUnit_zero_ne_zero : specialCuspUnit 0 ≠ 0 :=
  TriangleSource.reciprocalCusp_tDivQ_zero_ne_zero triangleSphereUniformization
    triangleSphereUniformization_cusp

theorem specialCuspCoordinate_eq_mul_unit (q : ℂ) :
    specialCuspCoordinate q = q * specialCuspUnit q :=
  MuTorsor.CuspCoordinates.t_eq_mul_tDivQ triangleSphereUniformization
    triangleSphereUniformization_cusp q

/-- The reciprocal of the actual finite coordinate is the actual source parameter times a unit. -/
theorem specialSourceCoordinate_inv_cusp :
    ∀ᶠ z in atImInfty,
      (specialSourceCoordinate z)⁻¹ = cuspQ z * specialCuspUnit (cuspQ z) :=
  MuTorsor.CuspCoordinates.inv_finiteProjection_eq_cuspQ_mul_tDivQ
    triangleSphereUniformization triangleSphereUniformization_cusp

/-- The exact derivative of the actual normalized source coordinate on high horodiscs. -/
theorem specialSourceCoordinate_scalarDeriv_cusp :
    ∀ᶠ z in atImInfty,
      scalarDeriv specialSourceCoordinate z =
        -cuspDerivativeScale * deriv specialCuspCoordinate (cuspQ z) /
          (cuspQ z * specialCuspUnit (cuspQ z) ^ 2) :=
  finiteProjection_scalarDeriv_cusp triangleSphereUniformization triangleSphereUniformization_cusp

/-- The actual finite source coordinate is unramified throughout a sufficiently high horodisc. -/
theorem specialSourceCoordinate_scalarDeriv_eventually_ne_zero :
    ∀ᶠ z in atImInfty, scalarDeriv specialSourceCoordinate z ≠ 0 := by
  filter_upwards [specialSourceCoordinate_scalarDeriv_cusp,
    eventually_cusp_germ_ne_zero specialCuspCoordinate_deriv_analyticAt_zero
      specialCuspCoordinate_deriv_ne_zero,
    eventually_cusp_germ_ne_zero specialCuspUnit_analyticAt_zero specialCuspUnit_zero_ne_zero]
      with z hz hD hU
  rw [hz]
  exact div_ne_zero (mul_ne_zero (neg_ne_zero.mpr cuspDerivativeScale_ne_zero) hD)
    (mul_ne_zero (cuspQ_ne_zero z) (pow_ne_zero 2 hU))

/-- The order-one normalized coefficient has an actual analytic cusp germ vanishing at zero. -/
theorem exists_cusp_germ_div_specialSource_deriv {A : ℍ → ℂ}
    (hA : HasCuspOrder 1 A) :
    ∃ G : ℂ → ℂ, AnalyticAt ℂ G 0 ∧ G 0 = 0 ∧
      ∀ᶠ z in atImInfty,
        A z / scalarDeriv specialSourceCoordinate z = G (cuspQ z) :=
  exists_cusp_germ_div_deriv_of_order_one cuspDerivativeScale_ne_zero
    specialCuspUnit_analyticAt_zero specialCuspUnit_zero_ne_zero
    specialCuspCoordinate_deriv_analyticAt_zero specialCuspCoordinate_deriv_ne_zero
    specialSourceCoordinate_scalarDeriv_cusp hA

/-- After clearing the two finite branch-coordinate factors, the normalized
order-two coefficient has an actual analytic cusp germ vanishing at zero. -/
theorem exists_cusp_germ_cleared_specialSource_cube {C : ℍ → ℂ}
    (hC : HasCuspOrder 2 C) :
    ∃ G : ℂ → ℂ, AnalyticAt ℂ G 0 ∧ G 0 = 0 ∧
      ∀ᶠ z in atImInfty,
        specialSourceCoordinate z ^ 2 * (specialSourceCoordinate z - 1) ^ 2 * C z /
          (scalarDeriv specialSourceCoordinate z) ^ 3 = G (cuspQ z) :=
  exists_cusp_germ_cleared_cube_of_order_two cuspDerivativeScale_ne_zero
    specialCuspUnit_analyticAt_zero specialCuspUnit_zero_ne_zero
    specialCuspCoordinate_deriv_analyticAt_zero specialCuspCoordinate_deriv_ne_zero
    specialSourceCoordinate_scalarDeriv_cusp specialSourceCoordinate_inv_cusp hC

end Wikipedia.HopfProblem.TriangleHolomorphicDifferentials
