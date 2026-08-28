import Wikipedia.HopfProblem.TriangleHolomorphicDifferentialsRegular
import Wikipedia.HopfProblem.TriangleHolomorphicDifferentialsTau

/-!
# Weight-one coefficients and the actual first-period differential

The source weight is the reciprocal determinant of the actual complex
period-covariance matrix. Squaring a weight-one one-form coefficient
and multiplying by the actual first-period derivative produces an
invariant cubic coefficient. All transformation laws here concern the
constructed triangle action and the constructed special periods.
-/

noncomputable section

open Set UpperHalfPlane
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.TriangleHolomorphicDifferentials

open SpecialPeriods

/-- The actual weight-one pullback law for a one-form coefficient. -/
def IsWeightOneDifferential (B : ℍ → ℂ) : Prop :=
  ∀ (g : TriangleGroup) (z : ℍ),
    B (triangleGeometricRepresentation g z) * actionDerivative g z =
      inverseDeterminantFactor g z * B z

/-- The coefficient of `ψ ⊗ ψ ⊗ dτ` in the literal upper-half-plane coordinate. -/
def weightOneCubic (B : ℍ → ℂ) (z : ℍ) : ℂ := B z ^ 2 * tauDerivative z

theorem weightOneCubic_holomorphic {B : ℍ → ℂ}
    (hB : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω B) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (weightOneCubic B) :=
  (hB.pow 2).mul tauDerivative_holomorphic

/-- The two reciprocal determinant factors cancel the actual determinant
square in the first-period derivative law. -/
theorem weightOneCubic_invariant {B : ℍ → ℂ} (hB : IsWeightOneDifferential B) :
    IsInvariantDifferential 3 (weightOneCubic B) := by
  intro g z
  change (B (triangleGeometricRepresentation g z) ^ 2 *
      tauDerivative (triangleGeometricRepresentation g z)) * actionDerivative g z ^ 3 =
    B z ^ 2 * tauDerivative z
  calc
    _ = (B (triangleGeometricRepresentation g z) * actionDerivative g z) ^ 2 *
        (tauDerivative (triangleGeometricRepresentation g z) * actionDerivative g z) := by ring
    _ = (inverseDeterminantFactor g z * B z) ^ 2 *
        (determinantFactor g z ^ 2 * tauDerivative z) := by
      rw [hB g z, tauDerivative_covariance]
    _ = (inverseDeterminantFactor g z * determinantFactor g z) ^ 2 *
        (B z ^ 2 * tauDerivative z) := by ring
    _ = B z ^ 2 * tauDerivative z := by
      rw [inverseDeterminantFactor_eq_inv, inv_mul_cancel₀ (determinantFactor_ne_zero g z)]
      simp

/-- The actual first-period expansion has order zero, so an order-one
weight coefficient gives order two for the invariant cubic. -/
theorem weightOneCubic_hasCuspOrder {B : ℍ → ℂ} (hB : HasCuspOrder 1 B) :
    HasCuspOrder 2 (weightOneCubic B) := by
  change HasCuspOrder 2 (fun z => B z ^ 2 * scalarDeriv specialTau z)
  simpa only [Nat.one_mul, Nat.add_zero] using
    (hB.pow 2).mul specialTau_scalarDeriv_hasCuspOrder_zero

/-- Equality on the proved dense regular locus determines a continuous
coefficient on the whole upper half-plane. -/
theorem eq_zero_of_regular {A : ℍ → ℂ} (hA : Continuous A)
    (hzero : ∀ z : ℍ, z ∈ triangleRegularLocus → A z = 0) : A = 0 := by
  have hc : closure triangleRegularLocus ⊆ {z : ℍ | A z = 0} :=
    closure_minimal hzero (isClosed_eq hA continuous_const)
  rw [triangleRegularLocus_dense.closure_eq] at hc
  funext z
  exact hc (mem_univ z)

/-- Vanishing of the actual cubic recovers the original coefficient:
the first-period derivative is nonzero on the actual dense regular locus. -/
theorem weightOne_eq_zero_of_cubic_eq_zero {B : ℍ → ℂ}
    (hB : Continuous B) (hC : weightOneCubic B = 0) : B = 0 := by
  apply eq_zero_of_regular hB
  intro z hz
  have he : B z ^ 2 * tauDerivative z = 0 := congrFun hC z
  have hn : tauDerivative z ≠ 0 := specialTau_scalarDeriv_ne_zero_of_regular hz
  exact sq_eq_zero_iff.mp ((mul_eq_zero.mp he).resolve_right hn)

end Wikipedia.HopfProblem.TriangleHolomorphicDifferentials
