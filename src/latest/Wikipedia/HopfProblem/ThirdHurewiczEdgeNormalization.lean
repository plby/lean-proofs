import Wikipedia.HopfProblem.ThirdHurewiczCoherentHomotopyConstants
import Wikipedia.HopfProblem.SecondHurewiczSimplyConnectedNormalization

/-!
# Extending the actual edge normalization through four-simplices

The frozen vertex and edge normalizations already exist through degree
three. The same genuine coherent extension supplies degree four. Constant
triangles and tetrahedra remain literal constant maps throughout.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.ThirdHurewicz

open FirstHurewicz SecondHurewicz.SimplyConnected

variable {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]

@[simp] theorem edgeTriangleHomotopy_const (x : X) :
    triangleEdgeStraighteningHomotopy x (ContinuousMap.const (Simplex 2) x) =
      ContinuousMap.const (I × Simplex 2) x :=
  extendCoherentSimplexHomotopy_const (stationarySimplexHomotopy 0)
    (edgeStraighteningHomotopy x) (edgeStraighteningHomotopy_face x)
    (edgeStraighteningHomotopy_zero x) x (edgeStraighteningHomotopy_const x)

@[simp] theorem edgeTetrahedronHomotopy_const (x : X) :
    tetrahedronEdgeStraighteningHomotopy x (ContinuousMap.const (Simplex 3) x) =
      ContinuousMap.const (I × Simplex 3) x :=
  extendCoherentSimplexHomotopy_const (edgeStraighteningHomotopy x)
    (triangleEdgeStraighteningHomotopy x) (triangleEdgeStraighteningHomotopy_face x)
    (triangleEdgeStraighteningHomotopy_zero x) x (edgeTriangleHomotopy_const x)

/-- The genuine four-simplex extension of the already constructed edge stage. -/
def edgeFourSimplexHomotopy (x : X) (smp : SingularSimplex X 4) :
    C(I × Simplex 4, X) :=
  extendCoherentSimplexHomotopy (triangleEdgeStraighteningHomotopy x)
    (tetrahedronEdgeStraighteningHomotopy x) (tetrahedronEdgeStraighteningHomotopy_face x)
    (tetrahedronEdgeStraighteningHomotopy_zero x) smp

@[simp] theorem edgeFourSimplexHomotopy_zero (x : X) (smp : SingularSimplex X 4)
    (s : Simplex 4) : edgeFourSimplexHomotopy x smp (0, s) = smp s :=
  extendCoherentSimplexHomotopy_zero _ _ _ _ smp s

theorem edgeFourSimplexHomotopy_face (x : X) :
    FaceCompatibleHomotopies 3 (tetrahedronEdgeStraighteningHomotopy x)
      (edgeFourSimplexHomotopy x) :=
  extendCoherentSimplexHomotopy_face (triangleEdgeStraighteningHomotopy x)
    (tetrahedronEdgeStraighteningHomotopy x) (tetrahedronEdgeStraighteningHomotopy_face x)
    (tetrahedronEdgeStraighteningHomotopy_zero x)

@[simp] theorem edgeFourSimplexHomotopy_const (x : X) :
    edgeFourSimplexHomotopy x (ContinuousMap.const (Simplex 4) x) =
      ContinuousMap.const (I × Simplex 4) x :=
  extendCoherentSimplexHomotopy_const (triangleEdgeStraighteningHomotopy x)
    (tetrahedronEdgeStraighteningHomotopy x) (tetrahedronEdgeStraighteningHomotopy_face x)
    (tetrahedronEdgeStraighteningHomotopy_zero x) x (edgeTetrahedronHomotopy_const x)

/-- The actual four-simplex after moving vertices and contracting edges. -/
def edgeNormalizedFourSimplexMap (x : X) (smp : SingularSimplex X 4) :
    SingularSimplex X 4 :=
  timeSlice (edgeFourSimplexHomotopy x (vertexNormalizedSimplex x 4 smp)) 1

/-- The four-simplex endpoint restricts to the frozen actual degree-three
endpoints on all five original faces. -/
theorem edgeNormalizedFourSimplexMap_face (x : X) (smp : SingularSimplex X 4)
    (i : Fin 5) :
    (edgeNormalizedFourSimplexMap x smp).comp (simplexFace 3 i) =
      normalizedTetrahedronMap x (smp.comp (simplexFace 3 i)) := by
  change (timeSlice (edgeFourSimplexHomotopy x
    (vertexNormalizedSimplex x 4 smp)) 1).comp (simplexFace 3 i) = _
  rw [timeSlice_face (edgeFourSimplexHomotopy_face x), vertexNormalizedSimplex_face]
  rfl

end Wikipedia.HopfProblem.ThirdHurewicz
