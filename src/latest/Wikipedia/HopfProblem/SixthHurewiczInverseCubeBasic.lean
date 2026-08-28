import Wikipedia.HopfProblem.SixthHurewiczCubeNormalization
import Wikipedia.HopfProblem.FourthHurewiczCubeSubdivisionRecoverySimplexBasic

/-!
# Native simplex restrictions of the actual normalized six-cube

The dimension-independent native subdivision uses the literal affine
permutation-simplex restrictions. Those are precisely the normalized
original six-simplices supplied by the genuine pasting construction.
-/

noncomputable section

open scoped Topology

namespace Wikipedia.HopfProblem.SixthHurewicz

open HigherHurewicz.CubeTriangulation HigherHurewicz.NativeSubdivision

variable {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
variable (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
  [Subsingleton (π_ 4 X x)] [Subsingleton (π_ 5 X x)]

theorem normalizedCube_simplex (p : GenLoop (Fin 6) X x) (e : Equiv.Perm (Fin 6)) :
    nativeBasedCubeSimplex (normalizedCube x p) (normalizedCube_internalBased x p) e =
      normalizedSixSimplex x (p.val.comp (cubeSimplex e)) := by
  apply Subtype.ext
  exact normalizedCube_cell x p e

end Wikipedia.HopfProblem.SixthHurewicz
