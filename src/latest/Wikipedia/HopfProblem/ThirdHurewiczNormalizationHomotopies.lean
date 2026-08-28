import Wikipedia.HopfProblem.ThirdHurewiczNormalizationHomotopiesBasic

/-!
# The actual full normalization homotopy on triangles and three-simplices

The constructed vertex, edge, and triangle stages concatenate to one
genuine coherent homotopy family. Its endpoint is the original normalized
three-simplex, and the constant triangle is fixed at every time.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.ThirdHurewicz

open FirstHurewicz SecondHurewicz.SimplyConnected

variable {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
variable (x : X) [Subsingleton (π_ 2 X x)]

/-- All three stages on actual singular triangles. -/
def normalizationTriangleHomotopy : SingularSimplex X 2 → C(I × Simplex 2, X) :=
  composeSimplexHomotopies (vertexEdgeTriangleHomotopy x) (triangleStraighteningHomotopy x)
    (vertexEdgeTriangleHomotopy_zero x) (triangleStraighteningHomotopy_zero x)

/-- All three stages on actual singular three-simplices. -/
def normalizationThreeSimplexHomotopy : SingularSimplex X 3 → C(I × Simplex 3, X) :=
  composeSimplexHomotopies (vertexEdgeThreeSimplexHomotopy x) (triangleThreeSimplexHomotopy x)
    (vertexEdgeThreeSimplexHomotopy_zero x) (triangleThreeSimplexHomotopy_zero x)

@[simp] theorem normalizationTriangleHomotopy_zero (smp : SingularSimplex X 2) (s : Simplex 2) :
    normalizationTriangleHomotopy x smp (0, s) = smp s :=
  composeSimplexHomotopies_zero _ _ _ _ smp s

@[simp] theorem normalizationThreeSimplexHomotopy_zero (smp : SingularSimplex X 3)
    (s : Simplex 3) : normalizationThreeSimplexHomotopy x smp (0, s) = smp s :=
  composeSimplexHomotopies_zero _ _ _ _ smp s

/-- The full families agree on every original face, at every time. -/
theorem normalizationHomotopy_face :
    FaceCompatibleHomotopies 2 (normalizationTriangleHomotopy x)
      (normalizationThreeSimplexHomotopy x) :=
  composeSimplexHomotopies_face (vertexEdgeTriangleHomotopy x)
    (triangleStraighteningHomotopy x) (vertexEdgeThreeSimplexHomotopy x)
    (triangleThreeSimplexHomotopy x) (vertexEdgeTriangleHomotopy_zero x)
    (triangleStraighteningHomotopy_zero x) (vertexEdgeThreeSimplexHomotopy_zero x)
    (triangleThreeSimplexHomotopy_zero x) (vertexEdgeHomotopy_face x)
    (triangleThreeSimplexHomotopy_face x)

/-- Literal constant-input stationarity, needed on the whole cube boundary. -/
@[simp] theorem normalizationTriangleHomotopy_const :
    normalizationTriangleHomotopy x (ContinuousMap.const (Simplex 2) x) =
      ContinuousMap.const (I × Simplex 2) x :=
  composeSimplexHomotopies_const (vertexEdgeTriangleHomotopy x)
    (triangleStraighteningHomotopy x) (vertexEdgeTriangleHomotopy_zero x)
    (triangleStraighteningHomotopy_zero x) x (vertexEdgeTriangleHomotopy_const x)
    (triangleStraighteningHomotopy_const x)

/-- Every final triangle is constant because its based native second
homotopy class was genuinely contracted. -/
@[simp] theorem normalizationTriangleHomotopy_endpoint (smp : SingularSimplex X 2) :
    timeSlice (normalizationTriangleHomotopy x smp) 1 = ContinuousMap.const (Simplex 2) x := by
  rw [normalizationTriangleHomotopy, timeSlice_composeSimplexHomotopies_one,
    vertexEdgeTriangleHomotopy_endpoint]
  ext s
  exact triangleStraighteningHomotopy_one x (normalizedTriangle x smp).val
    (normalizedTriangle x smp).property s

/-- The full homotopy has exactly the endpoint used in the genuine chain normalization. -/
@[simp] theorem normalizationThreeSimplexHomotopy_endpoint (smp : SingularSimplex X 3) :
    timeSlice (normalizationThreeSimplexHomotopy x smp) 1 = (normalizedThreeSimplex x smp).val := by
  rw [normalizationThreeSimplexHomotopy, timeSlice_composeSimplexHomotopies_one,
    vertexEdgeThreeSimplexHomotopy_endpoint]
  rfl

end Wikipedia.HopfProblem.ThirdHurewicz
