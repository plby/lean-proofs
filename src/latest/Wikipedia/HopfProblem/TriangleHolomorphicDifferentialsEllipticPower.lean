import Wikipedia.HopfProblem.TriangleHolomorphicDifferentialsPower
import Wikipedia.HopfProblem.EllipticBundleCharacters
import Wikipedia.HopfProblem.EllipticDiscOrbits
import Wikipedia.HopfProblem.SpecialPeriodsTriangleQuotientEllipticCharts

/-!
# Power descent at the actual elliptic points

The chosen Cayley charts conjugate the actual stabilizer generators to
the rotations with multipliers `-rho` and `-I`.  Their primitive orders
are three and four.  The scalar cyclic-descent theorems therefore apply
to these existing charts and their literal quotient coordinates `t = s^m`.
-/

noncomputable section

open Filter Topology
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.TriangleHolomorphicDifferentials

open SpecialPeriods SpecialPeriods.Triangle Elliptic

attribute [local instance] triangleGeometricAction

/-- The multipliers of the actual elliptic families are primitive of the
actual stabilizer orders: `-rho` of order three and `-I` of order four. -/
theorem elliptic_rotation_isPrimitiveRoot (j : Kind) :
    IsPrimitiveRoot (normalPhase j) j.order := by
  cases j
  · exact neg_rho_isPrimitiveRoot
  · exact Complex.isPrimitiveRoot_neg_I

/-- The existing normalized Cayley chart sends the actual generator to
multiplication by the corresponding primitive root. -/
theorem elliptic_chart_generator_val (j : Kind) (z : ellipticNeighborhood j) :
    letI := ellipticNeighborhoodAction j
    (ellipticNeighborhoodChart j (ellipticStabilizerGenerator j • z) : ℂ) =
      normalPhase j * (ellipticNeighborhoodChart j z : ℂ) := by
  let := ellipticNeighborhoodAction j
  rw [ellipticNeighborhoodChart_generator, familyRotation_val]

/-- The actual coordinate of the quotient projection is exactly the
power of the actual upstairs Cayley coordinate. -/
theorem elliptic_chart_projection_power (j : Kind) (z : ellipticNeighborhood j) :
    ellipticFullChart j (triangleOrbitProjection z) =
      (ellipticNeighborhoodChart j z : ℂ) ^ j.order := by
  rw [ellipticFullChart_projection, ellipticNeighborhoodChart_val]
  rfl

/-- The differential of the scalar rotation is its actual multiplier. -/
theorem elliptic_rotation_hasDerivAt (j : Kind) (s : ℂ) :
    HasDerivAt (fun w : ℂ => normalPhase j * w) (normalPhase j) s :=
  hasDerivAt_const_mul (normalPhase j)

/-- Generator covariance of coefficients in the actual neighborhood
chart gives the scalar germ covariance needed by cyclic descent. -/
theorem elliptic_chart_coefficient_covariance (j : Kind) {F : ℂ → ℂ} {k : ℕ}
    (hcov : letI := ellipticNeighborhoodAction j
      ∀ z : ellipticNeighborhood j,
        F (ellipticNeighborhoodChart j (ellipticStabilizerGenerator j • z) : ℂ) *
            normalPhase j ^ k = F (ellipticNeighborhoodChart j z : ℂ)) :
    ∀ᶠ s in 𝓝 (0 : ℂ), F (normalPhase j * s) * normalPhase j ^ k = F s := by
  let := ellipticNeighborhoodAction j
  have hdisc : (unitDisc : Set ℂ) ∈ 𝓝 (0 : ℂ) :=
    unitDisc.isOpen.mem_nhds Elliptic.discZero.property
  filter_upwards [hdisc] with s hs
  have hz := hcov ((ellipticNeighborhoodChart j).symm ⟨s, hs⟩)
  rw [elliptic_chart_generator_val, Diffeomorph.apply_symm_apply] at hz
  exact hz

/-- Scalar invariant germs at either actual elliptic point descend
holomorphically through its order-three or order-four quotient map. -/
theorem elliptic_scalar_power_descent (j : Kind) {F : ℂ → ℂ}
    (hF : AnalyticAt ℂ F 0)
    (hcov : ∀ᶠ s in 𝓝 (0 : ℂ), F (normalPhase j * s) = F s) :
    ∃ H : ℂ → ℂ, AnalyticAt ℂ H 0 ∧
      ∀ᶠ s in 𝓝 (0 : ℂ), F s = H (s ^ j.order) :=
  analyticAt_factor_through_pow j.order_pos (elliptic_rotation_isPrimitiveRoot j) hF hcov

/-- An invariant one-form in either actual elliptic chart has an analytic
coefficient downstairs, with the literal derivative factor of `s^m`. -/
theorem elliptic_oneForm_power_descent (j : Kind) {F : ℂ → ℂ}
    (hF : AnalyticAt ℂ F 0)
    (hcov : ∀ᶠ s in 𝓝 (0 : ℂ), F (normalPhase j * s) * normalPhase j = F s) :
    ∃ H : ℂ → ℂ, AnalyticAt ℂ H 0 ∧
      ∀ᶠ s in 𝓝 (0 : ℂ),
        F s = (j.order : ℂ) * s ^ (j.order - 1) * H (s ^ j.order) :=
  analyticAt_oneForm_power_descent j.order_pos
    (elliptic_rotation_isPrimitiveRoot j) hF hcov

/-- The analytic numerator regularizing a descended cubic at the actual
elliptic points.  Its initial exponent is zero at order three and one at
order four, as forced by the actual primitive-root covariance. -/
theorem elliptic_cubic_numerator_power_descent (j : Kind) {F : ℂ → ℂ}
    (hF : AnalyticAt ℂ F 0)
    (hcov : ∀ᶠ s in 𝓝 (0 : ℂ), F (normalPhase j * s) * normalPhase j ^ 3 = F s) :
    ∃ H : ℂ → ℂ, AnalyticAt ℂ H 0 ∧
      ∀ᶠ s in 𝓝 (0 : ℂ),
        F s = (j.order : ℂ) ^ 3 * s ^ (j.order - 3) * H (s ^ j.order) :=
  analyticAt_cubic_power_descent (by cases j <;> decide)
    (elliptic_rotation_isPrimitiveRoot j) hF hcov

/-- An invariant cubic in either actual elliptic chart descends to a
meromorphic coefficient whose pole has order at most two. -/
theorem elliptic_cubic_power_descent (j : Kind) {F : ℂ → ℂ}
    (hF : AnalyticAt ℂ F 0)
    (hcov : ∀ᶠ s in 𝓝 (0 : ℂ), F (normalPhase j * s) * normalPhase j ^ 3 = F s) :
    ∃ K : ℂ → ℂ, MeromorphicAt K 0 ∧
      (-2 : WithTop ℤ) ≤ meromorphicOrderAt K 0 ∧
      ∀ᶠ s in 𝓝[≠] (0 : ℂ),
        F s = ((j.order : ℂ) * s ^ (j.order - 1)) ^ 3 * K (s ^ j.order) :=
  meromorphicAt_cubic_power_descent (by cases j <;> decide)
    (elliptic_rotation_isPrimitiveRoot j) hF hcov

/-- D0 directly from generator invariance in the actual Cayley chart. -/
theorem elliptic_scalar_descent_of_chart_invariant (j : Kind) {F : ℂ → ℂ}
    (hF : AnalyticAt ℂ F 0)
    (hcov : letI := ellipticNeighborhoodAction j
      ∀ z : ellipticNeighborhood j,
        F (ellipticNeighborhoodChart j (ellipticStabilizerGenerator j • z) : ℂ) =
          F (ellipticNeighborhoodChart j z : ℂ)) :
    ∃ H : ℂ → ℂ, AnalyticAt ℂ H 0 ∧
      ∀ᶠ s in 𝓝 (0 : ℂ), F s = H (s ^ j.order) := by
  apply elliptic_scalar_power_descent j hF
  have h := elliptic_chart_coefficient_covariance j (k := 0) (F := F)
    (by simpa only [pow_zero, mul_one] using hcov)
  simpa only [pow_zero, mul_one] using h

/-- D1 directly from weighted generator covariance in the actual chart. -/
theorem elliptic_oneForm_descent_of_chart_covariance (j : Kind) {F : ℂ → ℂ}
    (hF : AnalyticAt ℂ F 0)
    (hcov : letI := ellipticNeighborhoodAction j
      ∀ z : ellipticNeighborhood j,
        F (ellipticNeighborhoodChart j (ellipticStabilizerGenerator j • z) : ℂ) *
            normalPhase j = F (ellipticNeighborhoodChart j z : ℂ)) :
    ∃ H : ℂ → ℂ, AnalyticAt ℂ H 0 ∧
      ∀ᶠ s in 𝓝 (0 : ℂ),
        F s = (j.order : ℂ) * s ^ (j.order - 1) * H (s ^ j.order) := by
  apply elliptic_oneForm_power_descent j hF
  have h := elliptic_chart_coefficient_covariance j (k := 1) (F := F)
    (by simpa only [pow_one] using hcov)
  simpa only [pow_one] using h

/-- D2 directly from cubic generator covariance in the actual chart,
including the actual meromorphic pole-order bound downstairs. -/
theorem elliptic_cubic_descent_of_chart_covariance (j : Kind) {F : ℂ → ℂ}
    (hF : AnalyticAt ℂ F 0)
    (hcov : letI := ellipticNeighborhoodAction j
      ∀ z : ellipticNeighborhood j,
        F (ellipticNeighborhoodChart j (ellipticStabilizerGenerator j • z) : ℂ) *
            normalPhase j ^ 3 = F (ellipticNeighborhoodChart j z : ℂ)) :
    ∃ K : ℂ → ℂ, MeromorphicAt K 0 ∧
      (-2 : WithTop ℤ) ≤ meromorphicOrderAt K 0 ∧
      ∀ᶠ s in 𝓝[≠] (0 : ℂ),
        F s = ((j.order : ℂ) * s ^ (j.order - 1)) ^ 3 * K (s ^ j.order) :=
  elliptic_cubic_power_descent j hF (elliptic_chart_coefficient_covariance j hcov)

end Wikipedia.HopfProblem.TriangleHolomorphicDifferentials
