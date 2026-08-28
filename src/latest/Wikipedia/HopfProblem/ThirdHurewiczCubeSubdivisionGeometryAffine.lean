import Wikipedia.HopfProblem.ThirdHurewiczCubeSubdivisionGeometry
import Wikipedia.HopfProblem.ThirdHurewiczEvaluation

/-!
# Affine realization of the interval-triangle prism inside the cube

The maps used by the existing singular cross product are identified with
literal barycentric interpolation in the native cube.  This includes
repeated vertices; no passage to normalized chains is made.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.ThirdHurewicz.Geometry

open FirstHurewicz SingularMayerVietoris PeriodTorusHigherHomology
open SecondHurewicz SecondHurewicz.SimplyConnected

/-- A zero-one vertex, as an actual point of the native three-cube. -/
def cubeBitVertex (v : Fin 3 → Fin 2) : Cube3 :=
  fun i => pathSimplex Path.id (stdVertices 1 (v i))

@[simp] theorem cubeBitVertex_coordinate (v : Fin 3 → Fin 2) (i : Fin 3) :
    (cubeBitVertex v i : ℝ) = stdVertices 1 (v i) 1 := rfl

@[simp] theorem cubeBitVertex_zero (v : Fin 3 → Fin 2) {i : Fin 3} (h : v i = 0) :
    cubeBitVertex v i = 0 := by
  simp [cubeBitVertex, h, stdVertices]

@[simp] theorem cubeBitVertex_one (v : Fin 3 → Fin 2) {i : Fin 3} (h : v i = 1) :
    cubeBitVertex v i = 1 := by
  simp [cubeBitVertex, h, stdVertices]

/-- The actual prism map of the oriented interval and a specified square triangle. -/
def cubeTrianglePrism (v : Fin 3 → Fin 2 × Fin 2) :
    C(Simplex 1 × Simplex 2, Cube3) :=
  cubeCoordinates.comp ((pathSimplex Path.id).prodMap
    (squareCoordinates.comp (squareAffineTriangle v)))

/-- Barycentric interpolation remains affine after selecting standard vertices. -/
theorem affineSimplex_comp_selectedVertices {m n p : ℕ}
    (v : Fin (n + 1) → Simplex p) (a : Fin (m + 1) → Fin (n + 1)) :
    (affineSimplex v).comp (affineSimplex (fun j => stdVertices n (a j))) =
      affineSimplex (fun j => v (a j)) := by
  rw [affineSimplex_comp]
  congr 1
  funext j
  exact affineSimplex_vertex v (a j)

/-- Every formal prism simplex has exactly its prescribed cube vertices. -/
theorem cubeTrianglePrism_affine {n : ℕ} (v : Fin 3 → Fin 2 × Fin 2)
    (w : Fin (n + 1) → Fin 2 × Fin 3) :
    (cubeTrianglePrism v).comp
        (productAffineSimplex (fun j => (stdVertices 1 (w j).1, stdVertices 2 (w j).2))) =
      cubeAffineSimplex (fun j => cubeBitVertex ![(w j).1, (v (w j).2).1, (v (w j).2).2]) := by
  ext s i
  fin_cases i
  · change affineSimplex (fun j => stdVertices 1 (w j).1) s 1 = _
    rw [affineSimplex_coordinate]
    simp [cubeAffineSimplex_coordinate, cubeBitVertex_coordinate]
  · change affineSimplex (fun j => stdVertices 1 (v j).1)
      (affineSimplex (fun j => stdVertices 2 (w j).2) s) 1 = _
    change ((affineSimplex (fun j => stdVertices 1 (v j).1)).comp
      (affineSimplex (fun j => stdVertices 2 (w j).2))) s 1 = _
    rw [affineSimplex_comp_selectedVertices, affineSimplex_coordinate]
    simp [cubeAffineSimplex_coordinate, cubeBitVertex_coordinate]
  · change affineSimplex (fun j => stdVertices 1 (v j).2)
      (affineSimplex (fun j => stdVertices 2 (w j).2) s) 1 = _
    change ((affineSimplex (fun j => stdVertices 1 (v j).2)).comp
      (affineSimplex (fun j => stdVertices 2 (w j).2))) s 1 = _
    rw [affineSimplex_comp_selectedVertices, affineSimplex_coordinate]
    simp [cubeAffineSimplex_coordinate, cubeBitVertex_coordinate]

/-- A repeated-vertex simplex on a fixed cube side is still supported on that side. -/
theorem cubeAffineSimplex_boundary_of_coordinate {n : ℕ}
    (v : Fin (n + 1) → Cube3) (i : Fin 3)
    (h : (∀ j, v j i = 0) ∨ (∀ j, v j i = 1)) (s : Simplex n) :
    cubeAffineSimplex v s ∈ Cube.boundary (Fin 3) := by
  rcases h with h | h
  · exact ⟨i, Or.inl (cubeAffineSimplex_constant_coordinate v i 0 h s)⟩
  · exact ⟨i, Or.inr (cubeAffineSimplex_constant_coordinate v i 1 h s)⟩

variable {X : Type} [TopologicalSpace X] {x : X}

theorem loop_comp_cubeAffineSimplex_of_coordinate {n : ℕ}
    (p : GenLoop (Fin 3) X x) (v : Fin (n + 1) → Cube3) (i : Fin 3)
    (h : (∀ j, v j i = 0) ∨ (∀ j, v j i = 1)) :
    p.val.comp (cubeAffineSimplex v) = ContinuousMap.const (Simplex n) x := by
  ext s
  exact GenLoop.boundary p _ (cubeAffineSimplex_boundary_of_coordinate v i h s)

end Wikipedia.HopfProblem.ThirdHurewicz.Geometry
