import Wikipedia.HopfProblem.FourthHurewiczChainClasses
import Wikipedia.HopfProblem.FourthHurewiczCubeSubdivisionChains

/-!
# The actual fourth-cube chain assignment is its signed simplex-class sum

The genuine recursive cross-product chain has the proved signed affine
simplex expansion. Applying the actual normalized chain-class operator
gives precisely the native permutation-cell sum used for recovery.
-/

noncomputable section

open scoped Topology

namespace Wikipedia.HopfProblem.FourthHurewicz

open FirstHurewicz HigherHurewicz.CubeTriangulation

variable {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
variable (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]

/-- Exact evaluation of the original four-cube chain under the normalized class assignment. -/
theorem fourSimplexClassOperator_cubeChain_sum (p : GenLoop (Fin 4) X x) :
    fourSimplexClassOperator x (cubeChain p) =
      ∑ e : Equiv.Perm (Fin 4), cubeOrientation e •
        basedFourSimplexClass (normalizedFourSimplex x (p.val.comp (cubeSimplex e))) := by
  rw [CubeSubdivision.cubeChain_eq_sum_simplices, map_sum]
  apply Finset.sum_congr rfl
  intro e _
  rw [map_zsmul, fourSimplexClassOperator_simplex]

end Wikipedia.HopfProblem.FourthHurewicz
