import Wikipedia.HopfProblem.SecondHurewiczSimplyConnectedSquareNormalizationGeometry
import Wikipedia.HopfProblem.SecondHurewiczSimplyConnectedEdge
import Wikipedia.HopfProblem.SecondHurewiczSimplyConnectedTriangleFaces

/-!
# Normalizing the two actual triangles of a native square

The original lower and upper triangles already have based vertices. Their
edge-straightening homotopies agree on the literal shared diagonal and stay
constant on the four outside edges. Pasting them therefore constructs an
actual homotopy of generalized loops relative to the square boundary.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.SecondHurewicz.SimplyConnected

open FirstHurewicz

variable {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X] {x : X}

/-- The actual lower triangle after edge straightening. -/
def squareNormalizedLowerTriangle (p : GenLoop (Fin 2) X x) : BasedTriangle x :=
  edgeStraightenedTriangle x (p.val.comp lowerSquareTriangle)
    (lowerSquareTriangle_verticesBased p)

/-- The actual upper triangle after edge straightening, retaining its original parametrization. -/
def squareNormalizedUpperTriangle (p : GenLoop (Fin 2) X x) : BasedTriangle x :=
  edgeStraightenedTriangle x (p.val.comp upperSquareTriangle)
    (upperSquareTriangle_verticesBased p)

@[simp] theorem squareNormalizedLowerTriangle_val (p : GenLoop (Fin 2) X x) :
    (squareNormalizedLowerTriangle p).val =
      timeSlice (triangleEdgeStraighteningHomotopy x (p.val.comp lowerSquareTriangle)) 1 := rfl

@[simp] theorem squareNormalizedUpperTriangle_val (p : GenLoop (Fin 2) X x) :
    (squareNormalizedUpperTriangle p).val =
      timeSlice (triangleEdgeStraighteningHomotopy x (p.val.comp upperSquareTriangle)) 1 := rfl

/-- Edge straightening as a genuine continuous-map homotopy to its based endpoint. -/
def squareNormalizationTriangleHomotopy (smp : C(Simplex 2, X))
    (h : VerticesBased x 2 smp) : smp.Homotopy (edgeStraightenedTriangle x smp h).val where
  toContinuousMap := triangleEdgeStraighteningHomotopy x smp
  map_zero_left := triangleEdgeStraighteningHomotopy_zero x smp
  map_one_left _ := rfl

@[simp] theorem squareNormalizationTriangleHomotopy_apply (smp : C(Simplex 2, X))
    (h : VerticesBased x 2 smp) (u : I × Simplex 2) :
    squareNormalizationTriangleHomotopy smp h u = triangleEdgeStraighteningHomotopy x smp u :=
  rfl

/-- The homotopy on the original lower triangle. -/
def squareLowerNormalizationHomotopy (p : GenLoop (Fin 2) X x) :
    (p.val.comp lowerSquareTriangle).Homotopy (squareNormalizedLowerTriangle p).val :=
  squareNormalizationTriangleHomotopy _ (lowerSquareTriangle_verticesBased p)

/-- The homotopy on the original upper triangle. -/
def squareUpperNormalizationHomotopy (p : GenLoop (Fin 2) X x) :
    (p.val.comp upperSquareTriangle).Homotopy (squareNormalizedUpperTriangle p).val :=
  squareNormalizationTriangleHomotopy _ (upperSquareTriangle_verticesBased p)

theorem squareNormalization_edge_face (smp : C(Simplex 2, X))
    (i : Fin 3) (r : I) (s : Simplex 1) :
    triangleEdgeStraighteningHomotopy x smp (r, simplexFace 1 i s) =
      edgeStraighteningHomotopy x (smp.comp (simplexFace 1 i)) (r, s) :=
  DFunLike.congr_fun (triangleEdgeStraighteningHomotopy_face x smp i) (r, s)

/-- The diagonal agreement is equality of the original edge maps before straightening. -/
theorem squareNormalization_diagonal (p : GenLoop (Fin 2) X x) (r : I) (s : Simplex 1) :
    squareLowerNormalizationHomotopy p (r, simplexFace 1 1 s) =
      squareUpperNormalizationHomotopy p (r, simplexFace 1 1 s) := by
  change triangleEdgeStraighteningHomotopy x (p.val.comp lowerSquareTriangle)
      (r, simplexFace 1 1 s) =
    triangleEdgeStraighteningHomotopy x (p.val.comp upperSquareTriangle)
      (r, simplexFace 1 1 s)
  rw [squareNormalization_edge_face, squareNormalization_edge_face, squareTriangles_diagonal]

/-- The two outside lower edges remain fixed throughout the actual homotopy. -/
theorem squareLowerNormalization_outerFace (p : GenLoop (Fin 2) X x)
    (r : I) (i : Fin 3) (hi : i ≠ 1) (s : Simplex 1) :
    squareLowerNormalizationHomotopy p (r, simplexFace 1 i s) = x := by
  change triangleEdgeStraighteningHomotopy x (p.val.comp lowerSquareTriangle)
    (r, simplexFace 1 i s) = x
  rw [squareNormalization_edge_face, lowerSquareTriangle_outerFace p i hi,
    edgeStraighteningHomotopy_const]
  rfl

/-- The two outside upper edges remain fixed throughout the actual homotopy. -/
theorem squareUpperNormalization_outerFace (p : GenLoop (Fin 2) X x)
    (r : I) (i : Fin 3) (hi : i ≠ 1) (s : Simplex 1) :
    squareUpperNormalizationHomotopy p (r, simplexFace 1 i s) = x := by
  change triangleEdgeStraighteningHomotopy x (p.val.comp upperSquareTriangle)
    (r, simplexFace 1 i s) = x
  rw [squareNormalization_edge_face, upperSquareTriangle_outerFace p i hi,
    edgeStraighteningHomotopy_const]
  rfl

/-- The boundary-fixed square homotopy is obtained by pasting the two actual triangle homotopies. -/
def squareNormalizationHomotopy (p : GenLoop (Fin 2) X x) :
    p.val.HomotopyRel
      (basedTrianglesLoop (squareNormalizedLowerTriangle p) (squareNormalizedUpperTriangle p)).val
      (Cube.boundary (Fin 2)) :=
  basedTrianglesHomotopy_of_faces (squareNormalizedLowerTriangle p)
    (squareNormalizedUpperTriangle p) (squareLowerNormalizationHomotopy p)
    (squareUpperNormalizationHomotopy p) (squareNormalization_diagonal p)
    (squareLowerNormalization_outerFace p) (squareUpperNormalization_outerFace p)

theorem squareNormalization_homotopic (p : GenLoop (Fin 2) X x) :
    GenLoop.Homotopic p
      (basedTrianglesLoop (squareNormalizedLowerTriangle p) (squareNormalizedUpperTriangle p)) :=
  ⟨squareNormalizationHomotopy p⟩

end Wikipedia.HopfProblem.SecondHurewicz.SimplyConnected
