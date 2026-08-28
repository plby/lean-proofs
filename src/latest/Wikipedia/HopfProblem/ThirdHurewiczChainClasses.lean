import Wikipedia.HopfProblem.ThirdHurewiczNormalization

/-!
# Assigning native third homotopy classes to actual singular chains

Each original singular three-simplex is sent to the native third homotopy
class of its actual whole-boundary normalization. This is an integral
linear map on the original singular chain group, not a replacement group
or an assumed inverse on homology.
-/

noncomputable section

open scoped Topology

namespace Wikipedia.HopfProblem.ThirdHurewicz

open FirstHurewicz

variable {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
variable (x : X) [Subsingleton (π_ 2 X x)]

/-- The native third-homotopy assignment, linearized on genuine singular chains. -/
def threeSimplexClassOperator : Chains X 3 →ₗ[ℤ] Additive (π_ 3 X x) :=
  chainLift X 3 fun smp => basedThreeSimplexClass (normalizedThreeSimplex x smp)

@[simp] theorem threeSimplexClassOperator_simplex (smp : SingularSimplex X 3) :
    threeSimplexClassOperator x (simplexChain X 3 smp) =
      basedThreeSimplexClass (normalizedThreeSimplex x smp) :=
  chainLift_simplex X 3 _ smp

@[simp] theorem threeSimplexClassOperator_constant :
    threeSimplexClassOperator x (simplexChain X 3 (ContinuousMap.const (Simplex 3) x)) = 0 := by
  rw [threeSimplexClassOperator_simplex, normalizedThreeSimplex_const,
    basedThreeSimplexClass_constant]

end Wikipedia.HopfProblem.ThirdHurewicz
