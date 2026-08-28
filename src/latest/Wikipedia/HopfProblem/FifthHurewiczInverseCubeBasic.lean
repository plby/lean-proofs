import Wikipedia.HopfProblem.FifthHurewiczCubeNormalization
import Wikipedia.HopfProblem.FourthHurewiczCubeSubdivisionRecoverySimplexBasic

/-!
# Native simplex restrictions of the actual normalized five-cube

The dimension-independent native subdivision uses the literal affine
permutation-simplex restrictions. Those are precisely the normalized
original five-simplices supplied by the genuine pasting construction.
-/

noncomputable section

open scoped Topology

namespace Wikipedia.HopfProblem.FifthHurewicz

open HigherHurewicz.CubeTriangulation HigherHurewicz.NativeSubdivision

variable {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
variable (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
  [Subsingleton (π_ 4 X x)]

theorem normalizedCube_simplex (p : GenLoop (Fin 5) X x) (e : Equiv.Perm (Fin 5)) :
    nativeBasedCubeSimplex (normalizedCube x p) (normalizedCube_internalBased x p) e =
      normalizedFiveSimplex x (p.val.comp (cubeSimplex e)) := by
  apply Subtype.ext
  exact normalizedCube_cell x p e

end Wikipedia.HopfProblem.FifthHurewicz
