import Wikipedia.HopfProblem.FifthHurewiczNormalization

/-!
# Native fifth-homotopy classes of actual normalized singular chains

The constructed based five-simplex determines its class in the original
native fifth homotopy group. Linearization uses the genuine free singular
chain group and retains the literal original normalized simplex maps.
-/

noncomputable section

open scoped Topology

namespace Wikipedia.HopfProblem.FifthHurewicz

open FirstHurewicz

variable {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
variable (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
  [Subsingleton (π_ 4 X x)]

/-- The actual native fifth-homotopy assignment on original singular five-chains. -/
def fiveSimplexClassOperator : Chains X 5 →ₗ[ℤ] Additive (π_ 5 X x) :=
  chainLift X 5 fun smp => basedFiveSimplexClass (normalizedFiveSimplex x smp)

@[simp] theorem fiveSimplexClassOperator_simplex (smp : SingularSimplex X 5) :
    fiveSimplexClassOperator x (simplexChain X 5 smp) =
      basedFiveSimplexClass (normalizedFiveSimplex x smp) :=
  chainLift_simplex X 5 _ smp

@[simp] theorem fiveSimplexClassOperator_constant :
    fiveSimplexClassOperator x (simplexChain X 5 (ContinuousMap.const (Simplex 5) x)) = 0 := by
  rw [fiveSimplexClassOperator_simplex, normalizedFiveSimplex_const]
  rfl

end Wikipedia.HopfProblem.FifthHurewicz
