import Wikipedia.HopfProblem.ThirdHurewiczNormalizationHomotopies

/-!
# Exact filling of a tetrahedron boundary in a two-connected target

The existing vertex, edge, and triangle homotopies are glued on the actual
boundary, without assuming an extension in advance. Their endpoint is
constant. Reversing this boundary homotopy and extending it from the
constant tetrahedron produces a filling with the prescribed boundary.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.OrbitPair.SimplexFilling

open FirstHurewicz ThirdHurewicz SecondHurewicz.SimplyConnected

theorem boundaryFace_comp {n : ℕ} (i j : Fin (n + 2)) (hij : i ≤ j) :
    (simplexFaceBoundary (n + 1) j.succ).comp (simplexFace n i) =
      (simplexFaceBoundary (n + 1) i.castSucc).comp (simplexFace n j) := by
  apply ContinuousMap.ext
  intro s
  apply Subtype.ext
  exact DFunLike.congr_fun (PeriodTorusLineBundle.ChernCocycle.simplexFace_comp hij) s

variable {X : Type} [TopologicalSpace X]

theorem boundaryFaceHomotopies_compatible {n : ℕ}
    (H : SingularSimplex X n → C(I × Simplex n, X))
    (H' : SingularSimplex X (n + 1) → C(I × Simplex (n + 1), X))
    (h : FaceCompatibleHomotopies n H H') (g : C(SimplexBoundary (n + 2), X)) :
    FaceCompatible (fun i => H' (g.comp (simplexFaceBoundary (n + 1) i))) := by
  apply faceCompatible_of_cofaceCompatible
  intro i j hij t s
  have hi := congrArg (fun F : C(I × Simplex n, X) => F (t, s))
    (h (g.comp (simplexFaceBoundary (n + 1) j.succ)) i)
  have hj := congrArg (fun F : C(I × Simplex n, X) => F (t, s))
    (h (g.comp (simplexFaceBoundary (n + 1) i.castSucc)) j)
  change H' (g.comp (simplexFaceBoundary (n + 1) j.succ)) (t, simplexFace n i s) =
    H ((g.comp (simplexFaceBoundary (n + 1) j.succ)).comp (simplexFace n i)) (t, s) at hi
  change H' (g.comp (simplexFaceBoundary (n + 1) i.castSucc)) (t, simplexFace n j s) =
    H ((g.comp (simplexFaceBoundary (n + 1) i.castSucc)).comp (simplexFace n j)) (t, s) at hj
  rw [hi, hj]
  change H (g.comp ((simplexFaceBoundary (n + 1) j.succ).comp (simplexFace n i))) (t, s) =
    H (g.comp ((simplexFaceBoundary (n + 1) i.castSucc).comp (simplexFace n j))) (t, s)
  rw [boundaryFace_comp i j hij]

variable [SimplyConnectedSpace X] (x : X)

def vertexEdgeEdgeHomotopy : SingularSimplex X 1 → C(I × Simplex 1, X) :=
  composeSimplexHomotopies (vertexStraighteningHomotopy x 1) (edgeStraighteningHomotopy x)
    (vertexStraighteningHomotopy_zero x 1) (edgeStraighteningHomotopy_zero x)

theorem vertexEdgeEdgeHomotopy_zero (smp : SingularSimplex X 1) (s : Simplex 1) :
    vertexEdgeEdgeHomotopy x smp (0, s) = smp s :=
  composeSimplexHomotopies_zero _ _ _ _ smp s

theorem vertexEdgeEdgeTriangle_face :
    FaceCompatibleHomotopies 1 (vertexEdgeEdgeHomotopy x) (vertexEdgeTriangleHomotopy x) :=
  composeSimplexHomotopies_face (vertexStraighteningHomotopy x 1) (edgeStraighteningHomotopy x)
    (vertexStraighteningHomotopy x 2) (triangleEdgeStraighteningHomotopy x)
    (vertexStraighteningHomotopy_zero x 1) (edgeStraighteningHomotopy_zero x)
    (vertexStraighteningHomotopy_zero x 2) (triangleEdgeStraighteningHomotopy_zero x)
    (vertexStraighteningHomotopy_face x 1) (triangleEdgeStraighteningHomotopy_face x)

def normalizationEdgeHomotopy : SingularSimplex X 1 → C(I × Simplex 1, X) :=
  composeSimplexHomotopies (vertexEdgeEdgeHomotopy x) (stationarySimplexHomotopy 1)
    (vertexEdgeEdgeHomotopy_zero x) (fun _ _ => rfl)

variable [Subsingleton (π_ 2 X x)]

theorem normalizationEdgeTriangle_face :
    FaceCompatibleHomotopies 1 (normalizationEdgeHomotopy x) (normalizationTriangleHomotopy x) :=
  composeSimplexHomotopies_face (vertexEdgeEdgeHomotopy x) (stationarySimplexHomotopy 1)
    (vertexEdgeTriangleHomotopy x) (triangleStraighteningHomotopy x)
    (vertexEdgeEdgeHomotopy_zero x) (fun _ _ => rfl)
    (vertexEdgeTriangleHomotopy_zero x) (triangleStraighteningHomotopy_zero x)
    (vertexEdgeEdgeTriangle_face x) (triangleStraighteningHomotopy_face x)

def boundaryContraction (g : C(SimplexBoundary 3, X)) : C(I × SimplexBoundary 3, X) :=
  glueFaceHomotopies (fun i => normalizationTriangleHomotopy x (g.comp (simplexFaceBoundary 2 i)))
    (boundaryFaceHomotopies_compatible (normalizationEdgeHomotopy x)
      (normalizationTriangleHomotopy x) (normalizationEdgeTriangle_face x) g)

theorem boundaryContraction_zero (g : C(SimplexBoundary 3, X)) (s : SimplexBoundary 3) :
    boundaryContraction x g (0, s) = g s := by
  obtain ⟨i, u, rfl⟩ := simplexBoundary_exists_face 2 s
  rw [boundaryContraction, glueFaceHomotopies_face, normalizationTriangleHomotopy_zero]
  rfl

theorem boundaryContraction_one (g : C(SimplexBoundary 3, X)) (s : SimplexBoundary 3) :
    boundaryContraction x g (1, s) = x := by
  obtain ⟨i, u, rfl⟩ := simplexBoundary_exists_face 2 s
  rw [boundaryContraction, glueFaceHomotopies_face]
  exact congrArg (fun F : C(Simplex 2, X) => F u)
    (normalizationTriangleHomotopy_endpoint x (g.comp (simplexFaceBoundary 2 i)))

include x in
theorem exists_boundary_extension (g : C(SimplexBoundary 3, X)) :
    ∃ F : C(Simplex 3, X), ∀ s : SimplexBoundary 3, F s.val = g s := by
  let H : (ContinuousMap.const (SimplexBoundary 3) x).Homotopy g := {
    toFun z := boundaryContraction x g (unitInterval.symm z.1, z.2)
    continuous_toFun := (boundaryContraction x g).continuous.comp
      ((unitInterval.continuous_symm.comp continuous_fst).prodMk continuous_snd)
    map_zero_left s := by
      rw [unitInterval.symm_zero]
      exact boundaryContraction_one x g s
    map_one_left s := by
      rw [unitInterval.symm_one]
      exact boundaryContraction_zero x g s }
  let h₀ (s : SimplexBoundary 3) : H.toContinuousMap (0, s) =
      (ContinuousMap.const (Simplex 3) x) s.val := H.apply_zero s
  refine ⟨boundaryExtensionEndpoint (ContinuousMap.const (Simplex 3) x) H.toContinuousMap h₀,
    fun s => ?_⟩
  exact (boundaryExtensionEndpoint_boundary _ _ _ s).trans (H.apply_one s)

end Wikipedia.HopfProblem.OrbitPair.SimplexFilling
