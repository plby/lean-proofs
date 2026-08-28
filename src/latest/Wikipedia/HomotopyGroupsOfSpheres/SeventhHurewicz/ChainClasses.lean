import Wikipedia.HomotopyGroupsOfSpheres.SeventhHurewicz.Normalization

/-!
# Native seventh-homotopy classes of actual normalized singular chains

The constructed based seven-simplex determines its class in the original
native seventh homotopy group. Linearization uses the genuine free singular
chain group and retains the literal original normalized simplex maps.
-/

noncomputable section

open scoped Topology

namespace Wikipedia.HomotopyGroupsOfSpheres.SeventhHurewicz

open Wikipedia.HopfProblem

open FirstHurewicz

variable {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
variable (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
  [Subsingleton (π_ 4 X x)] [Subsingleton (π_ 5 X x)] [Subsingleton (π_ 6 X x)]

/-- The actual native seventh-homotopy assignment on original singular seven-chains. -/
def sevenSimplexClassOperator : Chains X 7 →ₗ[ℤ] Additive (π_ 7 X x) :=
  chainLift X 7 fun smp => basedSevenSimplexClass (normalizedSevenSimplex x smp)

@[simp] theorem sevenSimplexClassOperator_simplex (smp : SingularSimplex X 7) :
    sevenSimplexClassOperator x (simplexChain X 7 smp) =
      basedSevenSimplexClass (normalizedSevenSimplex x smp) :=
  chainLift_simplex X 7 _ smp

@[simp] theorem sevenSimplexClassOperator_constant :
    sevenSimplexClassOperator x (simplexChain X 7 (ContinuousMap.const (Simplex 7) x)) = 0 := by
  rw [sevenSimplexClassOperator_simplex, normalizedSevenSimplex_const]
  rfl

end Wikipedia.HomotopyGroupsOfSpheres.SeventhHurewicz
