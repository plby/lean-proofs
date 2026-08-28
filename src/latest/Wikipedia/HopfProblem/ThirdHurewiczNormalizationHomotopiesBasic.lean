import Wikipedia.HopfProblem.ThirdHurewiczNormalization
import Wikipedia.HopfProblem.ThirdHurewiczHomotopyComposition

/-!
# Concatenating the actual vertex and edge stages

These are genuine simplex homotopies, not only endpoint maps. Native
homotopy concatenation retains exact face restrictions and fixes the
constant triangle throughout, so the families can be pasted on a cube.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.ThirdHurewicz

open FirstHurewicz SecondHurewicz.SimplyConnected

variable {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X] (x : X)

def vertexEdgeTriangleHomotopy : SingularSimplex X 2 → C(I × Simplex 2, X) :=
  composeSimplexHomotopies (vertexStraighteningHomotopy x 2)
    (triangleEdgeStraighteningHomotopy x) (vertexStraighteningHomotopy_zero x 2)
    (triangleEdgeStraighteningHomotopy_zero x)

def vertexEdgeThreeSimplexHomotopy : SingularSimplex X 3 → C(I × Simplex 3, X) :=
  composeSimplexHomotopies (vertexStraighteningHomotopy x 3)
    (tetrahedronEdgeStraighteningHomotopy x) (vertexStraighteningHomotopy_zero x 3)
    (tetrahedronEdgeStraighteningHomotopy_zero x)

@[simp] theorem vertexEdgeTriangleHomotopy_zero (smp : SingularSimplex X 2) (s : Simplex 2) :
    vertexEdgeTriangleHomotopy x smp (0, s) = smp s :=
  composeSimplexHomotopies_zero _ _ _ _ smp s

@[simp] theorem vertexEdgeThreeSimplexHomotopy_zero (smp : SingularSimplex X 3)
    (s : Simplex 3) : vertexEdgeThreeSimplexHomotopy x smp (0, s) = smp s :=
  composeSimplexHomotopies_zero _ _ _ _ smp s

theorem vertexEdgeHomotopy_face :
    FaceCompatibleHomotopies 2 (vertexEdgeTriangleHomotopy x)
      (vertexEdgeThreeSimplexHomotopy x) :=
  composeSimplexHomotopies_face (vertexStraighteningHomotopy x 2)
    (triangleEdgeStraighteningHomotopy x) (vertexStraighteningHomotopy x 3)
    (tetrahedronEdgeStraighteningHomotopy x) (vertexStraighteningHomotopy_zero x 2)
    (triangleEdgeStraighteningHomotopy_zero x) (vertexStraighteningHomotopy_zero x 3)
    (tetrahedronEdgeStraighteningHomotopy_zero x) (vertexStraighteningHomotopy_face x 2)
    (tetrahedronEdgeStraighteningHomotopy_face x)

@[simp] theorem vertexEdgeTriangleHomotopy_const :
    vertexEdgeTriangleHomotopy x (ContinuousMap.const (Simplex 2) x) =
      ContinuousMap.const (I × Simplex 2) x :=
  composeSimplexHomotopies_const (vertexStraighteningHomotopy x 2)
    (triangleEdgeStraighteningHomotopy x) (vertexStraighteningHomotopy_zero x 2)
    (triangleEdgeStraighteningHomotopy_zero x) x (vertexStraighteningHomotopy_const x 2)
    (edgeTriangleHomotopy_const x)

@[simp] theorem vertexEdgeTriangleHomotopy_endpoint (smp : SingularSimplex X 2) :
    timeSlice (vertexEdgeTriangleHomotopy x smp) 1 = (normalizedTriangle x smp).val := by
  rw [vertexEdgeTriangleHomotopy, timeSlice_composeSimplexHomotopies_one]
  rfl

@[simp] theorem vertexEdgeThreeSimplexHomotopy_endpoint (smp : SingularSimplex X 3) :
    timeSlice (vertexEdgeThreeSimplexHomotopy x smp) 1 = normalizedTetrahedronMap x smp := by
  rw [vertexEdgeThreeSimplexHomotopy, timeSlice_composeSimplexHomotopies_one]
  rfl

end Wikipedia.HopfProblem.ThirdHurewicz
