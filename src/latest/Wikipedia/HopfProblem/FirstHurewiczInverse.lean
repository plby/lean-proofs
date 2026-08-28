import Wikipedia.HopfProblem.FirstHurewiczChains
import Wikipedia.HopfProblem.FirstHurewiczTrianglePaths
import Wikipedia.HopfProblem.FirstHurewiczPathAbelianization

/-!
# The inverse first Hurewicz map on actual singular homology

An auxiliary path from the basepoint to each point closes every singular
edge to a based loop. Extending its abelianized class over the actual
singular chain coproduct kills the actual boundaries of singular triangles.
The resulting map therefore descends to Mathlib's integral first homology.
-/

noncomputable section

namespace Wikipedia.HopfProblem.FirstHurewicz

variable {X : Type} [TopologicalSpace X] {b x y : X}

/-- Endpoint casts do not change the closed, abelianized class of a path. -/
theorem basedLoopClass_cast (r : ∀ x : X, Path b x) (p : Path x y)
    {x' y' : X} (hx : x' = x) (hy : y' = y) :
    basedLoopClass r (p.cast hx hy) = basedLoopClass r p := by
  cases hx
  cases hy
  rfl

/-- Converting a path to a simplex and back preserves the path, with the
endpoint casts supplied by its actual vertices. -/
theorem simplexPath_pathSimplex_cast (p : Path x y) :
    simplexPath (pathSimplex p) =
      p.cast (pathSimplex_vertex_zero p) (pathSimplex_vertex_one p) := by
  apply Path.ext
  funext t
  change p (stdSimplexHomeomorphUnitInterval
    (stdSimplexHomeomorphUnitInterval.symm t)) = p t
  rw [Homeomorph.apply_symm_apply]

@[simp] theorem basedLoopClass_simplexPath_pathSimplex
    (r : ∀ x : X, Path b x) (p : Path x y) :
    basedLoopClass r (simplexPath (pathSimplex p)) = basedLoopClass r p := by
  rw [simplexPath_pathSimplex_cast, basedLoopClass_cast]

/-- The vertex casts used to concatenate triangle faces have no effect on
their closed abelianized classes. -/
theorem basedLoopClass_triangleFacePath (r : ∀ x : X, Path b x)
    (σ : SingularSimplex X 2) (i : Fin 3) :
    basedLoopClass r (triangleFacePath σ i) =
      basedLoopClass r (simplexPath (σ.comp (simplexFace 1 i))) :=
  basedLoopClass_cast r (simplexPath (σ.comp (simplexFace 1 i))) _ _

/-- The linear cochain on the actual singular chain coproduct that closes
each edge to a loop and takes its abelianized fundamental-group class. -/
def edgeLoopCochain (r : ∀ x : X, Path b x) :
    Chains X 1 →ₗ[ℤ] AbelianPi1 X b :=
  chainLift X 1 (fun σ => basedLoopClass r (simplexPath σ))

@[simp] theorem edgeLoopCochain_simplex (r : ∀ x : X, Path b x)
    (σ : SingularSimplex X 1) :
    edgeLoopCochain r (simplexChain X 1 σ) = basedLoopClass r (simplexPath σ) :=
  chainLift_simplex X 1 (fun σ => basedLoopClass r (simplexPath σ)) σ

@[simp] theorem edgeLoopCochain_pathSimplex (r : ∀ x : X, Path b x) (p : Path x y) :
    edgeLoopCochain r (simplexChain X 1 (pathSimplex p)) = basedLoopClass r p := by
  rw [edgeLoopCochain_simplex, basedLoopClass_simplexPath_pathSimplex]

/-- On an already based loop, the cochain gives its canonical abelianized class. -/
@[simp] theorem edgeLoopCochain_loopSimplex (r : ∀ x : X, Path b x) (p : Path b b) :
    edgeLoopCochain r (simplexChain X 1 (pathSimplex p)) = loopClass p := by
  rw [edgeLoopCochain_pathSimplex, basedLoopClass_loop]

/-- The actual three oriented faces of a singular triangle have total class zero. -/
theorem edgeLoopCochain_boundaryTwo_simplex (r : ∀ x : X, Path b x)
    (σ : SingularSimplex X 2) :
    edgeLoopCochain r (boundaryTwo X (simplexChain X 2 σ)) = 0 := by
  simp only [boundaryTwo_simplex, map_add, map_sub, edgeLoopCochain_simplex]
  change basedLoopClass r (simplexPath (σ.comp (simplexFace 1 0))) -
      basedLoopClass r (simplexPath (σ.comp (simplexFace 1 1))) +
      basedLoopClass r (simplexPath (σ.comp (simplexFace 1 2))) = 0
  have he := congrArg₂ (fun a c : AbelianPi1 X b => a + c)
    (congrArg₂ (fun a c : AbelianPi1 X b => a - c)
      (basedLoopClass_triangleFacePath r σ 0) (basedLoopClass_triangleFacePath r σ 1))
    (basedLoopClass_triangleFacePath r σ 2)
  exact he.symm.trans (basedLoopClass_triangle_boundary r
    (triangleEdge01 σ) (triangleEdge12 σ) (triangleEdge02 σ) (triangleEdges_homotopic σ))

/-- The edge cochain annihilates the actual degree-two differential. -/
theorem edgeLoopCochain_comp_boundaryTwo (r : ∀ x : X, Path b x) :
    (edgeLoopCochain r).comp (boundaryTwo X) = 0 := by
  apply chainMap_ext X 2
  intro σ
  exact edgeLoopCochain_boundaryTwo_simplex r σ

theorem edgeLoopCochain_boundaryTwo (r : ∀ x : X, Path b x) (c : Chains X 2) :
    edgeLoopCochain r (boundaryTwo X c) = 0 :=
  LinearMap.congr_fun (edgeLoopCochain_comp_boundaryTwo r) c

/-- The inverse first Hurewicz map, constructed on the actual categorical
singular homology object by descending the edge cochain on cycles. -/
def inverseHurewiczMap (r : ∀ x : X, Path b x) :
    SingularH1 X →ₗ[ℤ] AbelianPi1 X b :=
  homologyDescOfChain X (edgeLoopCochain r) (edgeLoopCochain_boundaryTwo r)

/-- Its value on the actual homology class of a cycle is the edge cochain value. -/
@[simp] theorem inverseHurewiczMap_cycleClass (r : ∀ x : X, Path b x)
    (c : Cycles1 X) :
    inverseHurewiczMap r (cycleClass X c) = edgeLoopCochain r c.1 :=
  homologyDescOfChain_cycleClass X (edgeLoopCochain r) (edgeLoopCochain_boundaryTwo r) c

@[simp] theorem inverseHurewiczMap_mkCycle (r : ∀ x : X, Path b x)
    (c : Chains X 1) (hc : boundaryOne X c = 0) :
    inverseHurewiczMap r (cycleClass X (mkCycle1 X c hc)) = edgeLoopCochain r c :=
  inverseHurewiczMap_cycleClass r _

end Wikipedia.HopfProblem.FirstHurewicz
