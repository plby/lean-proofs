import Wikipedia.HomotopyGroupsOfSpheres.SeventhHurewicz.CubeNormalization
import Wikipedia.HopfProblem.FourthHurewiczCubeSubdivisionRecoverySimplexBasic

/-!
# Native simplex restrictions of the actual normalized seven-cube

The dimension-independent native subdivision uses the literal affine
permutation-simplex restrictions. Those are precisely the normalized
original seven-simplices supplied by the genuine pasting construction.
-/

noncomputable section

open scoped Topology

namespace Wikipedia.HomotopyGroupsOfSpheres.SeventhHurewicz

open Wikipedia.HopfProblem

open HigherHurewicz.CubeTriangulation HigherHurewicz.NativeSubdivision

variable {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
variable (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
  [Subsingleton (π_ 4 X x)] [Subsingleton (π_ 5 X x)] [Subsingleton (π_ 6 X x)]

theorem normalizedCube_simplex (p : GenLoop (Fin 7) X x) (e : Equiv.Perm (Fin 7)) :
    nativeBasedCubeSimplex (normalizedCube x p) (normalizedCube_internalBased x p) e =
      normalizedSevenSimplex x (p.val.comp (cubeSimplex e)) := by
  apply Subtype.ext
  exact normalizedCube_cell x p e

end Wikipedia.HomotopyGroupsOfSpheres.SeventhHurewicz
