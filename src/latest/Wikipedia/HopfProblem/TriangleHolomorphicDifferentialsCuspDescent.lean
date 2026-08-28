import Wikipedia.HopfProblem.TriangleHolomorphicDifferentialsCuspOrder
import Wikipedia.HopfProblem.TriangleHolomorphicDifferentialsCuspCoordinatesDerivative
import Wikipedia.HopfProblem.TriangleHolomorphicDifferentialsPowerPole

/-!
# Differential coefficients in the actual cusp coordinate

The source exponential parameter `cuspQ` is the actual filled-cusp chart
coordinate. Its literal derivative converts first-order vanishing of a
one-form coefficient into an analytic cusp coefficient. Second-order
vanishing of a cubic coefficient gives a meromorphic cusp coefficient
with at most a simple pole. These are direct local coordinate formulas;
no global descent or vanishing conclusion is assumed.
-/

noncomputable section

open Filter Topology UpperHalfPlane

namespace Wikipedia.HopfProblem.TriangleHolomorphicDifferentials

open SpecialPeriods SpecialPeriods.Triangle

/-- The factor in the cusp pullback formulas is the literal derivative
of the actual exponential cusp coordinate. -/
theorem scalarDeriv_cuspQ (z : ℍ) :
    scalarDeriv cuspQ z = cuspDerivativeScale * cuspQ z := by
  simpa only [scalarDeriv, cuspDerivativeScale, mul_comm] using
    (cuspQ_hasStrictDerivAt z).hasDerivAt.deriv

/-- A one-form coefficient of actual cusp order one has an analytic
coefficient in the filled cusp coordinate. -/
theorem HasCuspOrder.exists_oneForm_cuspDescent {A : ℍ → ℂ}
    (hA : HasCuspOrder 1 A) :
    ∃ K : ℂ → ℂ, AnalyticAt ℂ K 0 ∧
      ∀ᶠ z in atImInfty,
        A z = (cuspDerivativeScale * cuspQ z) * K (cuspQ z) := by
  obtain ⟨R, hR, he⟩ := hA
  refine ⟨fun q => R q / cuspDerivativeScale, hR.div_const, ?_⟩
  filter_upwards [he] with z hz
  rw [hz, pow_one]
  field_simp [cuspDerivativeScale_ne_zero]

/-- A cubic coefficient of actual cusp order two descends near the
filled cusp with meromorphic order at least `-1`. The displayed cubic
factor is the third power of the actual derivative `dq/dz`. -/
theorem HasCuspOrder.exists_cubic_cuspDescent {C : ℍ → ℂ}
    (hC : HasCuspOrder 2 C) :
    ∃ K : ℂ → ℂ, MeromorphicAt K 0 ∧
      (-1 : WithTop ℤ) ≤ meromorphicOrderAt K 0 ∧
      ∀ᶠ z in atImInfty,
        C z = (cuspDerivativeScale * cuspQ z) ^ 3 * K (cuspQ z) := by
  obtain ⟨R, hR, he⟩ := hC
  have hnum : AnalyticAt ℂ (fun q => R q / cuspDerivativeScale ^ 3) 0 := hR.div_const
  refine ⟨fun q => R q / (cuspDerivativeScale ^ 3 * q), ?_, ?_, ?_⟩
  · simpa only [pow_one, div_div] using meromorphicAt_div_coordinate_pow hnum 1
  · simpa only [pow_one, Nat.cast_one, div_div] using
      meromorphicOrderAt_div_coordinate_pow_ge hnum 1
  · filter_upwards [he] with z hz
    rw [hz]
    field_simp [cuspDerivativeScale_ne_zero, cuspQ_ne_zero z]

end Wikipedia.HopfProblem.TriangleHolomorphicDifferentials
