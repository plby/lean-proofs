import Wikipedia.HopfProblem.FourthHurewiczCubeSubdivisionNativeChamberExtension
import Wikipedia.HopfProblem.FourthHurewiczCubeSubdivisionNativeDuffyOrdered

/-!
# Canonical charts for the coordinate-insertion induction

The ordered Duffy map has exactly the boundary-face conditions preserved
by inserting a coordinate. The relative affine homotopies therefore let
each stage of the induction use these canonical charts.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.HigherHurewicz.NativeSubdivision

/-- The canonical ordered Duffy map, together with its actual face conditions. -/
def orderedDuffyChart {n : ℕ} (e : Equiv.Perm (Fin n)) : NativeChamberChart e where
  toContinuousMap := nativeOrderedDuffyMap e
  zero_last := nativeOrderedDuffyMap_zero_last e
  zero_adjacent := nativeOrderedDuffyMap_zero_adjacent e
  one_first := nativeOrderedDuffyMap_one_first e
  one_adjacent := nativeOrderedDuffyMap_one_adjacent e

@[simp] theorem orderedDuffyChart_toContinuousMap {n : ℕ} (e : Equiv.Perm (Fin n)) :
    (orderedDuffyChart e).toContinuousMap = nativeOrderedDuffyMap e := rfl

theorem NativeChamberChart.commonOrderedDuffy {n : ℕ} {e : Equiv.Perm (Fin n)}
    (chart : NativeChamberChart e) (u : NativeCube (Fin n))
    (hu : u ∈ Cube.boundary (Fin n)) :
    NativeCubeSameFlat (chart.toContinuousMap u) (nativeOrderedDuffyMap e u) :=
  chart.sameFlat (orderedDuffyChart e) u hu

end Wikipedia.HopfProblem.HigherHurewicz.NativeSubdivision
