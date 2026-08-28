import Wikipedia.HopfProblem.SecondHurewiczSimplyConnectedVertexNormalization
import Wikipedia.HopfProblem.SecondHurewiczSimplyConnectedEdge

/-!
# Actual based-triangle normalization of singular simplices

First the vertices are moved to the base point. Then the resulting based
edges are contracted. The two already constructed coherent homotopies
produce actual based singular triangles and an exactly compatible map on
tetrahedra. No homotopy or homology comparison theorem is assumed.
-/

noncomputable section

open scoped unitInterval Topology

namespace Wikipedia.HopfProblem.SecondHurewicz.SimplyConnected

open FirstHurewicz

variable {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]

/-- The actual endpoint after the vertex-moving stage. -/
def vertexNormalizedSimplex (x : X) (n : ℕ) (smp : SingularSimplex X n) :
    SingularSimplex X n := timeSlice (vertexStraighteningHomotopy x n smp) 1

theorem vertexNormalizedSimplex_verticesBased (x : X) (n : ℕ)
    (smp : SingularSimplex X n) : VerticesBased x n (vertexNormalizedSimplex x n smp) :=
  vertexStraighteningHomotopy_one_verticesBased x n smp

theorem vertexNormalizedSimplex_face (x : X) (n : ℕ)
    (smp : SingularSimplex X (n + 1)) (i : Fin (n + 2)) :
    (vertexNormalizedSimplex x (n + 1) smp).comp (simplexFace n i) =
      vertexNormalizedSimplex x n (smp.comp (simplexFace n i)) :=
  vertexStraighteningHomotopy_timeSlice_face x n smp i 1

theorem vertexNormalizedSimplex_of_verticesBased (x : X) (n : ℕ)
    (smp : SingularSimplex X n) (h : VerticesBased x n smp) :
    vertexNormalizedSimplex x n smp = smp :=
  vertexStraighteningHomotopy_timeSlice_of_verticesBased x n smp h 1

/-- The actual triangle obtained by the two normalization stages. -/
def normalizedTriangle (x : X) (smp : SingularSimplex X 2) : BasedTriangle x :=
  edgeStraightenedTriangle x (vertexNormalizedSimplex x 2 smp)
    (vertexNormalizedSimplex_verticesBased x 2 smp)

@[simp] theorem normalizedTriangle_val (x : X) (smp : SingularSimplex X 2) :
    (normalizedTriangle x smp).val =
      timeSlice (triangleEdgeStraighteningHomotopy x (vertexNormalizedSimplex x 2 smp)) 1 :=
  rfl

/-- Vertex normalization is literally absent on an already vertex-based
triangle, which is needed to recover the original cubical representative. -/
theorem normalizedTriangle_of_verticesBased (x : X) (smp : SingularSimplex X 2)
    (h : VerticesBased x 2 smp) :
    normalizedTriangle x smp = edgeStraightenedTriangle x smp h := by
  apply Subtype.ext
  change timeSlice (triangleEdgeStraighteningHomotopy x (vertexNormalizedSimplex x 2 smp)) 1 =
    timeSlice (triangleEdgeStraighteningHomotopy x smp) 1
  rw [vertexNormalizedSimplex_of_verticesBased x 2 smp h]

/-- The actual tetrahedron endpoint after the same two stages. -/
def normalizedTetrahedronMap (x : X) (smp : SingularSimplex X 3) :
    SingularSimplex X 3 :=
  timeSlice (tetrahedronEdgeStraighteningHomotopy x (vertexNormalizedSimplex x 3 smp)) 1

/-- Every tetrahedron face is exactly the normalized original face. -/
theorem normalizedTetrahedronMap_face (x : X) (smp : SingularSimplex X 3) (i : Fin 4) :
    (normalizedTetrahedronMap x smp).comp (simplexFace 2 i) =
      (normalizedTriangle x (smp.comp (simplexFace 2 i))).val := by
  change (timeSlice (tetrahedronEdgeStraighteningHomotopy x
    (vertexNormalizedSimplex x 3 smp)) 1).comp (simplexFace 2 i) = _
  rw [timeSlice_face (tetrahedronEdgeStraighteningHomotopy_face x),
    vertexNormalizedSimplex_face]
  rfl

theorem normalizedTetrahedronMap_face_boundary (x : X) (smp : SingularSimplex X 3)
    (i : Fin 4) (s : Simplex 2) (hs : s ∈ triangleBoundary) :
    normalizedTetrahedronMap x smp (simplexFace 2 i s) = x := by
  have hf := congrArg (fun f : C(Simplex 2, X) => f s)
    (normalizedTetrahedronMap_face x smp i)
  exact hf.trans ((normalizedTriangle x (smp.comp (simplexFace 2 i))).property s hs)

end Wikipedia.HopfProblem.SecondHurewicz.SimplyConnected
