import Wikipedia.HopfProblem.FourthHurewiczCubeNormalization
import Wikipedia.HopfProblem.FourthHurewiczCubeSubdivisionRecoverySimplexBasic

/-!
# The genuine native subdivision cells of the normalized four-cube

The simplex used in native recovery is exactly the normalized original
singular four-simplex. Equality is proved on the actual continuous maps;
their boundary proofs are merely subtype properties.
-/

noncomputable section

open scoped Topology

namespace Wikipedia.HopfProblem.FourthHurewicz

open HigherHurewicz.CubeTriangulation HigherHurewicz.NativeSubdivision

variable {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
variable (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]

/-- Native subdivision sees the exact normalized original permutation simplex. -/
theorem normalizedCube_simplex (p : GenLoop (Fin 4) X x) (e : Equiv.Perm (Fin 4)) :
    nativeBasedCubeSimplex (normalizedCube x p) (normalizedCube_internalBased x p) e =
      normalizedFourSimplex x (p.val.comp (cubeSimplex e)) := by
  apply Subtype.ext
  exact normalizedCube_cell x p e

end Wikipedia.HopfProblem.FourthHurewicz
