import Wikipedia.HopfProblem.SixthHurewiczNormalization

/-!
# Native sixth-homotopy classes of actual normalized singular chains

The constructed based six-simplex determines its class in the original
native sixth homotopy group. Linearization uses the genuine free singular
chain group and retains the literal original normalized simplex maps.
-/

noncomputable section

open scoped Topology

namespace Wikipedia.HopfProblem.SixthHurewicz

open FirstHurewicz

variable {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
variable (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
  [Subsingleton (π_ 4 X x)] [Subsingleton (π_ 5 X x)]

/-- The actual native sixth-homotopy assignment on original singular six-chains. -/
def sixSimplexClassOperator : Chains X 6 →ₗ[ℤ] Additive (π_ 6 X x) :=
  chainLift X 6 fun smp => basedSixSimplexClass (normalizedSixSimplex x smp)

@[simp] theorem sixSimplexClassOperator_simplex (smp : SingularSimplex X 6) :
    sixSimplexClassOperator x (simplexChain X 6 smp) =
      basedSixSimplexClass (normalizedSixSimplex x smp) :=
  chainLift_simplex X 6 _ smp

@[simp] theorem sixSimplexClassOperator_constant :
    sixSimplexClassOperator x (simplexChain X 6 (ContinuousMap.const (Simplex 6) x)) = 0 := by
  rw [sixSimplexClassOperator_simplex, normalizedSixSimplex_const]
  rfl

end Wikipedia.HopfProblem.SixthHurewicz
