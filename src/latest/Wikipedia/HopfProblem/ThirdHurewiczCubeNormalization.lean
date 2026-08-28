import Wikipedia.HopfProblem.ThirdHurewiczNormalizationHomotopies
import Wikipedia.HopfProblem.ThirdHurewiczCubeGluing
import Wikipedia.HopfProblem.ThirdHurewiczCubeSubdivisionNativeBasic

/-!
# Genuine normalization of the native cube relative to its whole boundary

The coherent full simplex homotopies paste over the six original affine
tetrahedra. Their endpoint restrictions are exactly the normalized original
three-simplices. Thus every coordinate-equality plane of the endpoint cube
is based, while its actual native homotopy class remains unchanged.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.ThirdHurewicz

open FirstHurewicz Geometry SecondHurewicz.SimplyConnected

/-- Equality of distinct cube coordinates lies on the boundary of every
ordered tetrahedron containing that point. -/
theorem cubeTetrahedron_coordinate_equality_boundary (e : Equiv.Perm (Fin 3))
    (s : Simplex 3) (i j : Fin 3) (hij : i ≠ j)
    (hu : cubeTetrahedron e s i = cubeTetrahedron e s j) :
    s ∈ threeSimplexBoundary := by
  obtain ⟨a, rfl⟩ := e.surjective i
  obtain ⟨b, rfl⟩ := e.surjective j
  have hab : a ≠ b := fun h => hij (congrArg e h)
  have hcoords : (fun k : Fin 3 => (cubeTetrahedron e s (e k) : ℝ)) =
      ![s 1 + s 2 + s 3, s 2 + s 3, s 3] := by
    funext k
    fin_cases k
    · exact cubeTetrahedron_coordinate_zero e s
    · exact cubeTetrahedron_coordinate_one e s
    · exact cubeTetrahedron_coordinate_two e s
  have hv := congrArg (fun t : I => (t : ℝ)) hu
  change (fun k : Fin 3 => (cubeTetrahedron e s (e k) : ℝ)) a =
    (fun k : Fin 3 => (cubeTetrahedron e s (e k) : ℝ)) b at hv
  rw [hcoords] at hv
  fin_cases a <;> fin_cases b
  all_goals try exact (hab rfl).elim
  all_goals
    dsimp at hv
    first
    | exact ⟨1, by linarith [stdSimplex.zero_le s 1, stdSimplex.zero_le s 2]⟩
    | exact ⟨2, by linarith [stdSimplex.zero_le s 1, stdSimplex.zero_le s 2]⟩

variable {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
variable (x : X) [Subsingleton (π_ 2 X x)]

/-- The actual endpoint generalized loop of the pasted full normalization. -/
def normalizedCube (p : GenLoop (Fin 3) X x) : GenLoop (Fin 3) X x :=
  CubeGluing.coherentCubeEndpoint (normalizationTriangleHomotopy x)
    (normalizationThreeSimplexHomotopy x) (normalizationHomotopy_face x)
    (normalizationTriangleHomotopy_const x) p

/-- Each original tetrahedron is exactly the actual normalized original simplex. -/
theorem normalizedCube_cell (p : GenLoop (Fin 3) X x) (e : Equiv.Perm (Fin 3)) :
    (normalizedCube x p).val.comp (cubeTetrahedron e) =
      (normalizedThreeSimplex x (p.val.comp (cubeTetrahedron e))).val := by
  exact (CubeGluing.coherentCubeEndpoint_cell (normalizationTriangleHomotopy x)
    (normalizationThreeSimplexHomotopy x) (normalizationHomotopy_face x)
    (normalizationTriangleHomotopy_const x) p e).trans
      (normalizationThreeSimplexHomotopy_endpoint x _)

/-- The full construction is a genuine homotopy relative to the original cube boundary. -/
def normalizationCubeHomotopy (p : GenLoop (Fin 3) X x) :
    p.val.HomotopyRel (normalizedCube x p).val (Cube.boundary (Fin 3)) :=
  CubeGluing.coherentCubeHomotopy (normalizationTriangleHomotopy x)
    (normalizationThreeSimplexHomotopy x) (normalizationHomotopy_face x)
    (normalizationTriangleHomotopy_const x) (normalizationThreeSimplexHomotopy_zero x) p

theorem normalizedCube_homotopic (p : GenLoop (Fin 3) X x) :
    GenLoop.Homotopic p (normalizedCube x p) := ⟨normalizationCubeHomotopy x p⟩

theorem normalizedCube_quotient (p : GenLoop (Fin 3) X x) :
    (⟦p⟧ : π_ 3 X x) = ⟦normalizedCube x p⟧ :=
  Quotient.sound (normalizedCube_homotopic x p)

theorem normalizedCube_cell_boundary (p : GenLoop (Fin 3) X x)
    (e : Equiv.Perm (Fin 3)) (s : Simplex 3) (hs : s ∈ threeSimplexBoundary) :
    normalizedCube x p (cubeTetrahedron e s) = x := by
  have h := congrArg (fun f : C(Simplex 3, X) => f s) (normalizedCube_cell x p e)
  exact h.trans ((normalizedThreeSimplex x (p.val.comp (cubeTetrahedron e))).property s hs)

/-- Every internal equality plane is genuinely based at the endpoint. -/
theorem normalizedCube_internalBased (p : GenLoop (Fin 3) X x) :
    NativeCubeInternalBased (normalizedCube x p) := by
  intro u i j hij hu
  obtain ⟨e, s, rfl⟩ := CubeTriangulation.exists_cubeTetrahedron u
  exact normalizedCube_cell_boundary x p e s
    (cubeTetrahedron_coordinate_equality_boundary e s i j hij hu)

end Wikipedia.HopfProblem.ThirdHurewicz
