import Wikipedia.HopfProblem.TriangleHolomorphicDifferentialsGeometryAction
import Wikipedia.HopfProblem.TriangleHolomorphicDifferentialsTauRegular
import Wikipedia.HopfProblem.SpecialPeriodsBetaTorsorDescent
import Wikipedia.HopfProblem.SpecialPeriodsMuTorsorSourceOrdersCore

/-!
# Differential coefficients on the actual regular triangle quotient

The normalized source coordinate and its derivative are taken from the
constructed triangle uniformization. Invariant scalar coefficients on the
regular locus descend to actual analytic functions on `ℂ \ {0, 1}`. The
construction uses the already proved orbit quotient, not a supplied
descent function.
-/

noncomputable section

open Set Filter Topology UpperHalfPlane
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.TriangleHolomorphicDifferentials

open SpecialPeriods SpecialPeriods.Triangle

attribute [local instance] triangleOrbitChartedSpace triangleCompactifiedChartedSpace

/-- Invariance of a scalar coefficient of a `p`-fold complex differential
means pullback by the actual holomorphic triangle action. -/
def IsInvariantDifferential (p : ℕ) (A : ℍ → ℂ) : Prop :=
  ∀ (g : TriangleGroup) (z : ℍ),
    A (triangleGeometricRepresentation g z) * actionDerivative g z ^ p = A z

theorem specialSourceCoordinate_invariant (g : TriangleGroup) (z : ℍ) :
    specialSourceCoordinate (triangleGeometricRepresentation g z) =
      specialSourceCoordinate z :=
  BetaTorsor.finiteProjection_invariant triangleSphereUniformization g z

/-- The derivative law follows by differentiating the actual quotient
coordinate's invariance. -/
theorem specialSourceCoordinate_derivative_invariant (g : TriangleGroup) (z : ℍ) :
    scalarDeriv specialSourceCoordinate (triangleGeometricRepresentation g z) *
      actionDerivative g z = scalarDeriv specialSourceCoordinate z := by
  have h := scalarDeriv_comp_action specialSourceCoordinate_holomorphic g z
  have he : specialSourceCoordinate ∘ triangleGeometricRepresentation g =
      specialSourceCoordinate := funext (specialSourceCoordinate_invariant g)
  rw [he] at h
  exact h.symm

@[simp] theorem specialSourceCoordinate_centerOne : specialSourceCoordinate centerOne = 0 :=
  MuTorsor.SourceOrders.finiteProjection_centerOne triangleSphereUniformization
    triangleSphereUniformization_cusp triangleSphereUniformization_centerOne

@[simp] theorem specialSourceCoordinate_centerTwo : specialSourceCoordinate centerTwo = 1 :=
  MuTorsor.SourceOrders.finiteProjection_centerTwo triangleSphereUniformization
    triangleSphereUniformization_cusp triangleSphereUniformization_centerTwo

theorem specialSourceCoordinate_eq_zero_iff (z : ℍ) :
    specialSourceCoordinate z = 0 ↔ triangleOrbitProjection z = triangleOrbitCenterOne :=
  MuTorsor.SourceOrders.finiteProjection_eq_zero_iff triangleSphereUniformization
    triangleSphereUniformization_cusp triangleSphereUniformization_centerOne z

theorem specialSourceCoordinate_eq_one_iff (z : ℍ) :
    specialSourceCoordinate z = 1 ↔ triangleOrbitProjection z = triangleOrbitCenterTwo :=
  MuTorsor.SourceOrders.finiteProjection_eq_one_iff triangleSphereUniformization
    triangleSphereUniformization_cusp triangleSphereUniformization_centerTwo z

/-- The two deleted values are exactly the two actual elliptic fibres. -/
theorem specialSourceCoordinate_regular_iff (z : ℍ) :
    z ∈ triangleRegularLocus ↔
      specialSourceCoordinate z ≠ 0 ∧ specialSourceCoordinate z ≠ 1 := by
  rw [← triangleOrbitProjection_mem_regularDomain_iff, triangleOrbitRegularDomain_mem_iff]
  simp only [ne_eq, specialSourceCoordinate_eq_zero_iff, specialSourceCoordinate_eq_one_iff]

theorem specialSourceCoordinate_surjective : Function.Surjective specialSourceCoordinate :=
  BetaTorsor.finiteProjection_surjective triangleSphereUniformization
    triangleSphereUniformization_cusp

/-- The actual finite descent, with arbitrary zero extension at the two
excluded marked values. Those values are not asserted to be removable yet. -/
def regularScalarDescent (f : ℍ → ℂ) : ℂ → ℂ :=
  BetaTorsor.finiteDescent triangleSphereUniformization triangleSphereUniformization_cusp
    triangleRegularDomain f

theorem regularScalarDescent_projection (f : ℍ → ℂ)
    (hInv : ∀ (g : TriangleGroup) (z : ℍ), z ∈ triangleRegularLocus →
      f (triangleGeometricRepresentation g z) = f z) {z : ℍ}
    (hz : z ∈ triangleRegularLocus) :
    regularScalarDescent f (specialSourceCoordinate z) = f z :=
  BetaTorsor.finiteDescent_projection triangleSphereUniformization
    triangleSphereUniformization_cusp triangleRegularDomain f
    triangleRegularLocus_invariant hInv hz

/-- Holomorphy on the actual regular covering yields analyticity in the
literal finite coordinate away from the two marked values. -/
theorem regularScalarDescent_analytic (f : ℍ → ℂ)
    (hInv : ∀ (g : TriangleGroup) (z : ℍ), z ∈ triangleRegularLocus →
      f (triangleGeometricRepresentation g z) = f z)
    (hf : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω f triangleRegularLocus)
    {t : ℂ} (ht0 : t ≠ 0) (ht1 : t ≠ 1) : AnalyticAt ℂ (regularScalarDescent f) t := by
  have h := BetaTorsor.finiteDescent_analytic triangleSphereUniformization
    triangleSphereUniformization_cusp triangleRegularDomain f
    triangleRegularLocus_invariant hInv hf
  apply h
  obtain ⟨z, rfl⟩ := specialSourceCoordinate_surjective t
  exact (BetaTorsor.finiteDescentDomain_projection triangleSphereUniformization
    triangleSphereUniformization_cusp triangleRegularDomain
    triangleRegularLocus_invariant z).mpr
      ((specialSourceCoordinate_regular_iff z).mpr ⟨ht0, ht1⟩)

/-- Dividing an invariant differential by the same power of the actual
source derivative gives an invariant scalar on the regular locus. -/
theorem differentialRatio_invariant {p : ℕ} {A : ℍ → ℂ}
    (hA : IsInvariantDifferential p A) (g : TriangleGroup) (z : ℍ) :
    A (triangleGeometricRepresentation g z) /
        scalarDeriv specialSourceCoordinate (triangleGeometricRepresentation g z) ^ p =
      A z / scalarDeriv specialSourceCoordinate z ^ p := by
  have hg := actionDerivative_ne_zero g z
  have hd := specialSourceCoordinate_derivative_invariant g z
  calc
    A (triangleGeometricRepresentation g z) /
        scalarDeriv specialSourceCoordinate (triangleGeometricRepresentation g z) ^ p =
      (A (triangleGeometricRepresentation g z) * actionDerivative g z ^ p) /
        (scalarDeriv specialSourceCoordinate (triangleGeometricRepresentation g z) ^ p *
          actionDerivative g z ^ p) := (mul_div_mul_right _ _ (pow_ne_zero p hg)).symm
    _ = A z / scalarDeriv specialSourceCoordinate z ^ p := by
      rw [← mul_pow, hd, hA g z]

theorem differentialRatio_holomorphic {p : ℕ} {A : ℍ → ℂ}
    (hA : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω A) :
    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω
      (fun z => A z / scalarDeriv specialSourceCoordinate z ^ p) triangleRegularLocus := by
  intro z hz
  exact ((hA z).div₀ ((scalarDeriv_holomorphic specialSourceCoordinate_holomorphic z).pow p)
    (pow_ne_zero p (specialSourceCoordinate_scalarDeriv_ne_zero_of_regular hz))).contMDiffWithinAt

end Wikipedia.HopfProblem.TriangleHolomorphicDifferentials
