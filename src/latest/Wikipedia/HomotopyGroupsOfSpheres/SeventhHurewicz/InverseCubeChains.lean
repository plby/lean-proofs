import Wikipedia.HomotopyGroupsOfSpheres.SeventhHurewicz.ChainClasses
import Wikipedia.HomotopyGroupsOfSpheres.SeventhHurewicz.CubeSubdivisionChains

/-!
# The actual seventh-cube chain assignment is its signed simplex-class sum

The genuine recursive cross-product chain has the proved signed affine
simplex expansion. Applying the actual normalized chain-class operator
gives precisely the native permutation-cell sum used for recovery.
-/

noncomputable section

open scoped Topology

namespace Wikipedia.HomotopyGroupsOfSpheres.SeventhHurewicz

open Wikipedia.HopfProblem

open FirstHurewicz HigherHurewicz.CubeTriangulation

variable {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
variable (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
  [Subsingleton (π_ 4 X x)] [Subsingleton (π_ 5 X x)] [Subsingleton (π_ 6 X x)]

/-- Exact evaluation of the original seven-cube chain under the normalized class assignment. -/
theorem sevenSimplexClassOperator_cubeChain_sum (p : GenLoop (Fin 7) X x) :
    sevenSimplexClassOperator x (cubeChain p) =
      ∑ e : Equiv.Perm (Fin 7), cubeOrientation e •
        basedSevenSimplexClass (normalizedSevenSimplex x (p.val.comp (cubeSimplex e))) := by
  rw [CubeSubdivision.cubeChain_eq_sum_simplices, map_sum]
  apply Finset.sum_congr rfl
  intro e _
  rw [map_zsmul, sevenSimplexClassOperator_simplex]

end Wikipedia.HomotopyGroupsOfSpheres.SeventhHurewicz
