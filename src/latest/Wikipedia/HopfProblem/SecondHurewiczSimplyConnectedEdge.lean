import Wikipedia.HopfProblem.SecondHurewiczSimplyConnectedEdgeExtension
import Wikipedia.HopfProblem.SecondHurewiczSimplyConnectedVertexBasic
import Wikipedia.HopfProblem.SecondHurewiczSimplyConnectedTriangleBasic

/-!
# Coherent edge straightening through dimension three

The actual edge nullhomotopies extend over all singular triangles and
tetrahedra. Every face identity is literal. When the original vertices
are based, the terminal triangle has its entire boundary based.
-/

noncomputable section

open scoped unitInterval Topology

namespace Wikipedia.HopfProblem.SecondHurewicz.SimplyConnected

open FirstHurewicz

variable {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]

/-- The genuine extension of the three edge homotopies over a triangle. -/
def triangleEdgeStraighteningHomotopy (x : X) (smp : SingularSimplex X 2) :
    C(I × Simplex 2, X) :=
  extendCoherentSimplexHomotopy (stationarySimplexHomotopy 0)
    (edgeStraighteningHomotopy x) (edgeStraighteningHomotopy_face x)
    (edgeStraighteningHomotopy_zero x) smp

@[simp] theorem triangleEdgeStraighteningHomotopy_zero (x : X)
    (smp : SingularSimplex X 2) (s : Simplex 2) :
    triangleEdgeStraighteningHomotopy x smp (0, s) = smp s :=
  extendCoherentSimplexHomotopy_zero _ _ _ _ smp s

theorem triangleEdgeStraighteningHomotopy_face (x : X) :
    FaceCompatibleHomotopies 1 (edgeStraighteningHomotopy x)
      (triangleEdgeStraighteningHomotopy x) :=
  extendCoherentSimplexHomotopy_face (stationarySimplexHomotopy 0)
    (edgeStraighteningHomotopy x) (edgeStraighteningHomotopy_face x)
    (edgeStraighteningHomotopy_zero x)

/-- The genuine extension of the four coherent triangle homotopies over
the tetrahedron, required to control actual degree-three boundaries. -/
def tetrahedronEdgeStraighteningHomotopy (x : X) (smp : SingularSimplex X 3) :
    C(I × Simplex 3, X) :=
  extendCoherentSimplexHomotopy (edgeStraighteningHomotopy x)
    (triangleEdgeStraighteningHomotopy x) (triangleEdgeStraighteningHomotopy_face x)
    (triangleEdgeStraighteningHomotopy_zero x) smp

@[simp] theorem tetrahedronEdgeStraighteningHomotopy_zero (x : X)
    (smp : SingularSimplex X 3) (s : Simplex 3) :
    tetrahedronEdgeStraighteningHomotopy x smp (0, s) = smp s :=
  extendCoherentSimplexHomotopy_zero _ _ _ _ smp s

theorem tetrahedronEdgeStraighteningHomotopy_face (x : X) :
    FaceCompatibleHomotopies 2 (triangleEdgeStraighteningHomotopy x)
      (tetrahedronEdgeStraighteningHomotopy x) :=
  extendCoherentSimplexHomotopy_face (edgeStraighteningHomotopy x)
    (triangleEdgeStraighteningHomotopy x) (triangleEdgeStraighteningHomotopy_face x)
    (triangleEdgeStraighteningHomotopy_zero x)

/-- Based vertices ensure that every terminal triangle edge is literally
the constant singular edge. -/
theorem triangleEdgeStraighteningHomotopy_one_face (x : X)
    (smp : SingularSimplex X 2) (h : VerticesBased x 2 smp) (i : Fin 3) :
    (timeSlice (triangleEdgeStraighteningHomotopy x smp) 1).comp (simplexFace 1 i) =
      ContinuousMap.const (Simplex 1) x := by
  rw [timeSlice_face (triangleEdgeStraighteningHomotopy_face x)]
  ext s
  exact edgeStraighteningHomotopy_one x (smp.comp (simplexFace 1 i))
    (h.face i 0) (h.face i 1) s

/-- The whole boundary is based, not only its vertices. -/
theorem triangleEdgeStraighteningHomotopy_one_boundary (x : X)
    (smp : SingularSimplex X 2) (h : VerticesBased x 2 smp)
    (s : Simplex 2) (hs : s ∈ triangleBoundary) :
    timeSlice (triangleEdgeStraighteningHomotopy x smp) 1 s = x := by
  obtain ⟨i, t, ht⟩ := simplexBoundary_exists_face 1 (⟨s, hs⟩ : SimplexBoundary 2)
  have he : simplexFace 1 i t = s := congrArg Subtype.val ht
  rw [← he]
  exact congrArg (fun f : C(Simplex 1, X) => f t)
    (triangleEdgeStraighteningHomotopy_one_face x smp h i)

/-- Bundling the actual terminal singular triangle as a based triangle. -/
def edgeStraightenedTriangle (x : X) (smp : SingularSimplex X 2)
    (h : VerticesBased x 2 smp) : BasedTriangle x :=
  ⟨timeSlice (triangleEdgeStraighteningHomotopy x smp) 1,
    triangleEdgeStraighteningHomotopy_one_boundary x smp h⟩

@[simp] theorem edgeStraightenedTriangle_val (x : X) (smp : SingularSimplex X 2)
    (h : VerticesBased x 2 smp) :
    (edgeStraightenedTriangle x smp h).val =
      timeSlice (triangleEdgeStraighteningHomotopy x smp) 1 := rfl

end Wikipedia.HopfProblem.SecondHurewicz.SimplyConnected
