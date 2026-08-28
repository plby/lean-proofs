import Wikipedia.HopfProblem.ThirdHurewiczEdgeNormalization
import Wikipedia.HopfProblem.ThirdHurewiczTriangleNormalization

/-!
# Actual whole-boundary normalization for degree-three singular chains

The three constructed stages move vertices to the base point, contract
based edges, and contract the resulting based triangles. The final actual
three-simplex has its whole boundary based. The four-simplex endpoint
restricts to the normalized original faces exactly.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.ThirdHurewicz

open FirstHurewicz SecondHurewicz.SimplyConnected

variable {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
variable (x : X) [Subsingleton (π_ 2 X x)]

/-- The actual three-simplex after all three coherent normalization stages. -/
def normalizedThreeSimplex (smp : SingularSimplex X 3) : BasedThreeSimplex x :=
  triangleStraightenedThreeSimplex x (normalizedTetrahedronMap x smp)
    (normalizedTetrahedronMap_face_boundary x smp)

@[simp] theorem normalizedThreeSimplex_val (smp : SingularSimplex X 3) :
    (normalizedThreeSimplex x smp).val =
      timeSlice (triangleThreeSimplexHomotopy x (normalizedTetrahedronMap x smp)) 1 := rfl

/-- Every stage fixes the literal constant simplex. -/
@[simp] theorem normalizedThreeSimplex_const :
    normalizedThreeSimplex x (ContinuousMap.const (Simplex 3) x) =
      constantBasedThreeSimplex x := by
  apply Subtype.ext
  change timeSlice (triangleThreeSimplexHomotopy x
    (timeSlice (tetrahedronEdgeStraighteningHomotopy x
      (timeSlice (vertexStraighteningHomotopy x 3 (ContinuousMap.const (Simplex 3) x)) 1)) 1)) 1 =
    ContinuousMap.const (Simplex 3) x
  rw [vertexStraighteningHomotopy_const]
  change timeSlice (triangleThreeSimplexHomotopy x
    (timeSlice (tetrahedronEdgeStraighteningHomotopy x
      (ContinuousMap.const (Simplex 3) x)) 1)) 1 = _
  rw [edgeTetrahedronHomotopy_const]
  change timeSlice (triangleThreeSimplexHomotopy x (ContinuousMap.const (Simplex 3) x)) 1 = _
  rw [triangleThreeSimplexHomotopy_const]
  rfl

/-- For already based vertices, the first stage has literally no effect. -/
theorem normalizedThreeSimplex_val_of_verticesBased (smp : SingularSimplex X 3)
    (h : VerticesBased x 3 smp) :
    (normalizedThreeSimplex x smp).val =
      timeSlice (triangleThreeSimplexHomotopy x
        (timeSlice (tetrahedronEdgeStraighteningHomotopy x smp) 1)) 1 := by
  rw [normalizedThreeSimplex_val]
  unfold normalizedTetrahedronMap
  rw [vertexNormalizedSimplex_of_verticesBased x 3 smp h]

/-- The genuine four-simplex endpoint under the same three stages. -/
def normalizedFourSimplexMap (smp : SingularSimplex X 4) : SingularSimplex X 4 :=
  timeSlice (triangleFourSimplexHomotopy x (edgeNormalizedFourSimplexMap x smp)) 1

theorem normalizedFourSimplexMap_face (smp : SingularSimplex X 4) (i : Fin 5) :
    (normalizedFourSimplexMap x smp).comp (simplexFace 3 i) =
      (normalizedThreeSimplex x (smp.comp (simplexFace 3 i))).val := by
  change (timeSlice (triangleFourSimplexHomotopy x
    (edgeNormalizedFourSimplexMap x smp)) 1).comp (simplexFace 3 i) = _
  rw [timeSlice_face (triangleFourSimplexHomotopy_face x), edgeNormalizedFourSimplexMap_face]
  rfl

theorem normalizedFourSimplexMap_face_boundary (smp : SingularSimplex X 4)
    (i : Fin 5) (s : Simplex 3) (hs : s ∈ threeSimplexBoundary) :
    normalizedFourSimplexMap x smp (simplexFace 3 i s) = x := by
  have hf := congrArg (fun f : C(Simplex 3, X) => f s)
    (normalizedFourSimplexMap_face x smp i)
  exact hf.trans ((normalizedThreeSimplex x (smp.comp (simplexFace 3 i))).property s hs)

end Wikipedia.HopfProblem.ThirdHurewicz
