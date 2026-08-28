import Wikipedia.HopfProblem.FourthHurewiczCubeSubdivisionNativeChamberDuffy
import Wikipedia.HopfProblem.FourthHurewiczCubeSubdivisionRecoverySimplexComparison

/-!
# Recovering the oriented actual simplex class from a chamber chart

At the final insertion stage there are no unused coordinates. The actual
common-face homotopy identifies the chart with the ordered simplex map,
and the native coordinate-permutation theorem supplies its orientation.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.HigherHurewicz.NativeSubdivision

variable {n : ℕ} [Nontrivial (Fin n)]
variable {X : Type*} [TopologicalSpace X] {x : X}

theorem nativeClass_chamber_eq_orientedSimplex (p : GenLoop (Fin n) X x)
    (hp : NativeCubeInternalBased p) (e : Equiv.Perm (Fin n))
    (chart : NativeChamberChart e) :
    nativeClass (extendedChamberLoop p hp (le_refl n) chart) =
      CubeTriangulation.cubeOrientation e •
        SimplexGeometry.basedSimplexClass (nativeBasedCubeSimplex p hp e) := by
  apply nativeClass_commonOrderedSimplex p hp e
    (extendCubeMap (le_refl n) chart.toContinuousMap)
    (extendedChamberMap_based p hp (le_refl n) chart)
  intro u hu
  rw [extendCubeMap_refl]
  exact chart.commonOrderedDuffy u hu

end Wikipedia.HopfProblem.HigherHurewicz.NativeSubdivision
