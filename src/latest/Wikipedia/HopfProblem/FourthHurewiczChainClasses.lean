import Wikipedia.HopfProblem.FourthHurewiczNormalization

/-!
# Native fourth-homotopy classes of normalized singular four-chains

The actual normalized four-simplex gives a class in Mathlib's native
fourth homotopy group. Linearizing that assignment gives a map on the
original free singular chain group. Descent to homology will use the
genuine signed six-face relation, not a boundary-vanishing assumption.
-/

noncomputable section

open scoped Topology

namespace Wikipedia.HopfProblem.FourthHurewicz

open FirstHurewicz

variable {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
variable (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]

/-- The actual native fourth-homotopy assignment on singular four-chains. -/
def fourSimplexClassOperator : Chains X 4 →ₗ[ℤ] Additive (π_ 4 X x) :=
  chainLift X 4 fun smp => basedFourSimplexClass (normalizedFourSimplex x smp)

@[simp] theorem fourSimplexClassOperator_simplex (smp : SingularSimplex X 4) :
    fourSimplexClassOperator x (simplexChain X 4 smp) =
      basedFourSimplexClass (normalizedFourSimplex x smp) :=
  chainLift_simplex X 4 _ smp

@[simp] theorem fourSimplexClassOperator_constant :
    fourSimplexClassOperator x (simplexChain X 4 (ContinuousMap.const (Simplex 4) x)) = 0 := by
  rw [fourSimplexClassOperator_simplex, normalizedFourSimplex_const]
  rfl

end Wikipedia.HopfProblem.FourthHurewicz
