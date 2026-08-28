import Wikipedia.HopfProblem.FirstHurewiczSimplex
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Analysis.Convex.Contractible

/-!
# The actual singular triangle path relation

The three oriented edges are the paths of the actual face maps of a
singular two-simplex. Their endpoints are cast to the images of vertices
`0`, `1`, and `2`. The concatenation relation is proved inside the convex
standard simplex and then mapped through the singular simplex.
-/

noncomputable section

namespace Wikipedia.HopfProblem.FirstHurewicz

/-- A face map sends each actual vertex to the corresponding retained vertex. -/
@[simp] theorem simplexFace_vertex (n : ℕ) (i : Fin (n + 2)) (k : Fin (n + 1)) :
    simplexFace n i (stdSimplex.vertex (S := ℝ) k) =
      stdSimplex.vertex (S := ℝ) (i.succAbove k) := by
  rw [simplexFace_apply, stdSimplex.map_vertex]

/-- The actual standard simplex is contractible by its real convexity. -/
theorem simplex_contractible (n : ℕ) : ContractibleSpace (Simplex n) :=
  (convex_stdSimplex ℝ (Fin (n + 1))).contractibleSpace
    ⟨(stdSimplex.vertex (S := ℝ) (0 : Fin (n + 1))).val,
      (stdSimplex.vertex (S := ℝ) (0 : Fin (n + 1))).property⟩

/-- In particular, each actual standard simplex is simply connected. -/
theorem simplex_simplyConnected (n : ℕ) : SimplyConnectedSpace (Simplex n) := by
  let _ := simplex_contractible n
  infer_instance

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- The path of a triangle face, with endpoints at the retained triangle vertices. -/
def triangleFacePath (σ : C(Simplex 2, X)) (i : Fin 3) :
    Path (σ (stdSimplex.vertex (S := ℝ) (i.succAbove (0 : Fin 2))))
      (σ (stdSimplex.vertex (S := ℝ) (i.succAbove (1 : Fin 2)))) :=
  (simplexPath (σ.comp (simplexFace 1 i))).cast
    (congrArg σ (simplexFace_vertex 1 i 0)).symm
    (congrArg σ (simplexFace_vertex 1 i 1)).symm

theorem triangleFacePath_eq_cast (σ : C(Simplex 2, X)) (i : Fin 3) :
    triangleFacePath σ i = (simplexPath (σ.comp (simplexFace 1 i))).cast
      (congrArg σ (simplexFace_vertex 1 i 0)).symm
      (congrArg σ (simplexFace_vertex 1 i 1)).symm := rfl

@[simp] theorem triangleFacePath_apply (σ : C(Simplex 2, X)) (i : Fin 3)
    (t : unitInterval) :
    triangleFacePath σ i t = σ (simplexFace 1 i (stdSimplexHomeomorphUnitInterval.symm t)) :=
  rfl

/-- The oriented edge `0 → 1` is face `2`. -/
abbrev triangleEdge01 (σ : C(Simplex 2, X)) :
    Path (σ (stdSimplex.vertex (S := ℝ) (0 : Fin 3)))
      (σ (stdSimplex.vertex (S := ℝ) (1 : Fin 3))) := triangleFacePath σ 2

/-- The oriented edge `1 → 2` is face `0`. -/
abbrev triangleEdge12 (σ : C(Simplex 2, X)) :
    Path (σ (stdSimplex.vertex (S := ℝ) (1 : Fin 3)))
      (σ (stdSimplex.vertex (S := ℝ) (2 : Fin 3))) := triangleFacePath σ 0

/-- The oriented edge `0 → 2` is face `1`. -/
abbrev triangleEdge02 (σ : C(Simplex 2, X)) :
    Path (σ (stdSimplex.vertex (S := ℝ) (0 : Fin 3)))
      (σ (stdSimplex.vertex (S := ℝ) (2 : Fin 3))) := triangleFacePath σ 1

theorem triangleEdge01_eq_cast (σ : C(Simplex 2, X)) :
    triangleEdge01 σ = (simplexPath (σ.comp (simplexFace 1 2))).cast
      (congrArg σ (simplexFace_vertex 1 2 0)).symm
      (congrArg σ (simplexFace_vertex 1 2 1)).symm := rfl

theorem triangleEdge12_eq_cast (σ : C(Simplex 2, X)) :
    triangleEdge12 σ = (simplexPath (σ.comp (simplexFace 1 0))).cast
      (congrArg σ (simplexFace_vertex 1 0 0)).symm
      (congrArg σ (simplexFace_vertex 1 0 1)).symm := rfl

theorem triangleEdge02_eq_cast (σ : C(Simplex 2, X)) :
    triangleEdge02 σ = (simplexPath (σ.comp (simplexFace 1 1))).cast
      (congrArg σ (simplexFace_vertex 1 1 0)).symm
      (congrArg σ (simplexFace_vertex 1 1 1)).symm := rfl

@[simp] theorem triangleEdge01_apply (σ : C(Simplex 2, X)) (t : unitInterval) :
    triangleEdge01 σ t = σ (simplexFace 1 2 (stdSimplexHomeomorphUnitInterval.symm t)) := rfl

@[simp] theorem triangleEdge12_apply (σ : C(Simplex 2, X)) (t : unitInterval) :
    triangleEdge12 σ t = σ (simplexFace 1 0 (stdSimplexHomeomorphUnitInterval.symm t)) := rfl

@[simp] theorem triangleEdge02_apply (σ : C(Simplex 2, X)) (t : unitInterval) :
    triangleEdge02 σ t = σ (simplexFace 1 1 (stdSimplexHomeomorphUnitInterval.symm t)) := rfl

/-- The actual face paths are natural under continuous maps. -/
theorem triangleFacePath_map (σ : C(Simplex 2, X)) (f : C(X, Y)) (i : Fin 3) :
    (triangleFacePath σ i).map f.continuous = triangleFacePath (f.comp σ) i := by
  apply Path.ext
  funext t
  rfl

theorem triangleEdge01_eq_map (σ : C(Simplex 2, X)) :
    triangleEdge01 σ = (triangleEdge01 (ContinuousMap.id (Simplex 2))).map σ.continuous := by
  apply Path.ext
  funext t
  rfl

theorem triangleEdge12_eq_map (σ : C(Simplex 2, X)) :
    triangleEdge12 σ = (triangleEdge12 (ContinuousMap.id (Simplex 2))).map σ.continuous := by
  apply Path.ext
  funext t
  rfl

theorem triangleEdge02_eq_map (σ : C(Simplex 2, X)) :
    triangleEdge02 σ = (triangleEdge02 (ContinuousMap.id (Simplex 2))).map σ.continuous := by
  apply Path.ext
  funext t
  rfl

/-- The actual concatenation of edges `01` and `12` is homotopic relative
endpoints to edge `02`; no triangle relation is postulated. -/
theorem triangleEdges_homotopic (σ : C(Simplex 2, X)) :
    ((triangleEdge01 σ).trans (triangleEdge12 σ)).Homotopic (triangleEdge02 σ) := by
  let _ := simplex_simplyConnected 2
  have h := SimplyConnectedSpace.paths_homotopic
    ((triangleEdge01 (ContinuousMap.id (Simplex 2))).trans
      (triangleEdge12 (ContinuousMap.id (Simplex 2))))
    (triangleEdge02 (ContinuousMap.id (Simplex 2)))
  have hmap := h.map σ
  rw [Path.map_trans] at hmap
  exact hmap

end Wikipedia.HopfProblem.FirstHurewicz
