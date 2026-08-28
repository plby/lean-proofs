import Wikipedia.HopfProblem.FifthHurewiczChainClasses
import Wikipedia.HopfProblem.FifthHurewiczCubeSubdivisionChains

/-!
# The actual fifth-cube chain assignment is its signed simplex-class sum

The genuine recursive cross-product chain has the proved signed affine
simplex expansion. Applying the actual normalized chain-class operator
gives precisely the native permutation-cell sum used for recovery.
-/

noncomputable section

open scoped Topology

namespace Wikipedia.HopfProblem.FifthHurewicz

open FirstHurewicz HigherHurewicz.CubeTriangulation

variable {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
variable (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
  [Subsingleton (π_ 4 X x)]

/-- Exact evaluation of the original five-cube chain under the normalized class assignment. -/
theorem fiveSimplexClassOperator_cubeChain_sum (p : GenLoop (Fin 5) X x) :
    fiveSimplexClassOperator x (cubeChain p) =
      ∑ e : Equiv.Perm (Fin 5), cubeOrientation e •
        basedFiveSimplexClass (normalizedFiveSimplex x (p.val.comp (cubeSimplex e))) := by
  rw [CubeSubdivision.cubeChain_eq_sum_simplices, map_sum]
  apply Finset.sum_congr rfl
  intro e _
  rw [map_zsmul, fiveSimplexClassOperator_simplex]

end Wikipedia.HopfProblem.FifthHurewicz
