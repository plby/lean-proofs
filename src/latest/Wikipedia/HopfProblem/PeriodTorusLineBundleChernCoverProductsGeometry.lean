import Wikipedia.HopfProblem.PeriodTorusLineBundleChernCover
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCrossProductFormalPrism
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyPontryaginProduct

/-!
# The actual four-term chain product of two positive period loops

The existing singular edge product cones its signed boundary. In degree
`1 × 1` its literal expansion has two nondegenerate triangles and two
degenerate triangles. We retain all four terms and their actual signs.
Their faces are the original positive period loops or the constant edge.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusLineBundle.ChernCover

open FirstHurewicz SingularMayerVietoris PeriodTorusHigherHomology
  PeriodTorusHigherHomologyPontryagin

/-- The existing cone construction, expanded literally in degree `1 × 1`. -/
theorem formalEdgeCrossProduct_one_expansion {V W : Type*}
    (v : Fin 2 → V) (w : Fin 2 → W) :
    formalEdgeCrossProduct 1 (formalSimplex v) (formalSimplex w) =
      formalSimplex ![(v 0, w 0), (v 1, w 0), (v 1, w 1)] -
        formalSimplex ![(v 0, w 0), (v 0, w 0), (v 0, w 1)] -
          formalSimplex ![(v 0, w 0), (v 0, w 1), (v 1, w 1)] +
            formalSimplex ![(v 0, w 0), (v 0, w 0), (v 1, w 0)] := by
  rw [formalEdgeCrossProduct_simplex_succ, formalPointCrossProduct_edge_boundary,
    formalBoundary_edge_simplex]
  simp only [map_sub, formalEdgeCrossProduct_zero_simplex_right, formalMap_simplex,
    formalCone_simplex]
  have hv0 : (fun i : Fin 2 => (v 0, w i)) = ![(v 0, w 0), (v 0, w 1)] := by
    funext i
    fin_cases i <;> rfl
  have hv1 : (fun i : Fin 2 => (v 1, w i)) = ![(v 1, w 0), (v 1, w 1)] := by
    funext i
    fin_cases i <;> rfl
  have hw0 : (fun i : Fin 2 => (v i, w 0)) = ![(v 0, w 0), (v 1, w 0)] := by
    funext i
    fin_cases i <;> rfl
  have hw1 : (fun i : Fin 2 => (v i, w 1)) = ![(v 0, w 1), (v 1, w 1)] := by
    funext i
    fin_cases i <;> rfl
  simp only [Function.comp_def, hv0, hv1, hw0, hw1]
  abel

/-- The four actual corners of the product of the two standard edges. -/
def productCorner (i j : Fin 2) : Simplex 1 × Simplex 1 :=
  (stdVertices 1 i, stdVertices 1 j)

/-- Realize an ordered product-vertex simplex, map by the two actual
positive period loops, and then apply the torus addition map. -/
def periodProductSimplex (p : PeriodDomain) (x y : Lattice) {n : ℕ}
    (v : Fin (n + 1) → Simplex 1 × Simplex 1) : SingularSimplex p.Torus n :=
  (additionMap p.Torus).comp
    (((pathSimplex (p.periodLoop x)).prodMap (pathSimplex (p.periodLoop y))).comp
      (productAffineSimplex v))

/-- Actual face restriction deletes the corresponding ordered product vertex. -/
theorem periodProductSimplex_face (p : PeriodDomain) (x y : Lattice) {n : ℕ}
    (v : Fin (n + 2) → Simplex 1 × Simplex 1) (i : Fin (n + 2)) :
    (periodProductSimplex p x y v).comp (simplexFace n i) =
      periodProductSimplex p x y (fun j => v (i.succAbove j)) := by
  simp only [periodProductSimplex, ContinuousMap.comp_assoc, productAffineSimplex_face]

theorem periodProductSimplex_face_zero (p : PeriodDomain) (x y : Lattice)
    (a b c : Simplex 1 × Simplex 1) :
    (periodProductSimplex p x y ![a, b, c]).comp (simplexFace 1 0) =
      periodProductSimplex p x y ![b, c] := by
  rw [periodProductSimplex_face]
  congr 1

theorem periodProductSimplex_face_two (p : PeriodDomain) (x y : Lattice)
    (a b c : Simplex 1 × Simplex 1) :
    (periodProductSimplex p x y ![a, b, c]).comp (simplexFace 1 2) =
      periodProductSimplex p x y ![a, b] := by
  rw [periodProductSimplex_face]
  congr 1
  funext i
  fin_cases i <;> rfl

/-- Either horizontal side maps to the original positive first period loop. -/
theorem periodProductSimplex_horizontal (p : PeriodDomain) (x y : Lattice) (j : Fin 2) :
    periodProductSimplex p x y ![productCorner 0 j, productCorner 1 j] =
      pathSimplex (p.periodLoop x) := by
  have hv : (fun i : Fin 2 => (![productCorner 0 j, productCorner 1 j] i).1) =
      stdVertices 1 := by
    funext i
    fin_cases i <;> rfl
  have hw : (fun i : Fin 2 => (![productCorner 0 j, productCorner 1 j] i).2) =
      fun _ => stdVertices 1 j := by
    funext i
    fin_cases i <;> rfl
  apply ContinuousMap.ext
  intro s
  change pathSimplex (p.periodLoop x) (affineSimplex _ s) +
      pathSimplex (p.periodLoop y) (affineSimplex _ s) = pathSimplex (p.periodLoop x) s
  rw [hv, hw, affineSimplex_stdVertices, affineSimplex_constant]
  change pathSimplex (p.periodLoop x) s +
    pathSimplex (p.periodLoop y) (stdVertices 1 j) = _
  fin_cases j <;> simp [stdVertices]

/-- Either vertical side maps to the original positive second period loop. -/
theorem periodProductSimplex_vertical (p : PeriodDomain) (x y : Lattice) (i : Fin 2) :
    periodProductSimplex p x y ![productCorner i 0, productCorner i 1] =
      pathSimplex (p.periodLoop y) := by
  have hv : (fun j : Fin 2 => (![productCorner i 0, productCorner i 1] j).1) =
      fun _ => stdVertices 1 i := by
    funext j
    fin_cases j <;> rfl
  have hw : (fun j : Fin 2 => (![productCorner i 0, productCorner i 1] j).2) =
      stdVertices 1 := by
    funext j
    fin_cases j <;> rfl
  apply ContinuousMap.ext
  intro s
  change pathSimplex (p.periodLoop x) (affineSimplex _ s) +
      pathSimplex (p.periodLoop y) (affineSimplex _ s) = pathSimplex (p.periodLoop y) s
  rw [hv, hw, affineSimplex_constant, affineSimplex_stdVertices]
  change pathSimplex (p.periodLoop x) (stdVertices 1 i) +
    pathSimplex (p.periodLoop y) s = _
  fin_cases i <;> simp [stdVertices]

/-- A repeated corner maps to the actual constant singular simplex at the torus origin. -/
theorem periodProductSimplex_constant (p : PeriodDomain) (x y : Lattice) {n : ℕ}
    (i j : Fin 2) :
    periodProductSimplex p x y (fun _ : Fin (n + 1) => productCorner i j) =
      ContinuousMap.const (Simplex n) (0 : p.Torus) := by
  apply ContinuousMap.ext
  intro s
  change pathSimplex (p.periodLoop x) (affineSimplex (fun _ => stdVertices 1 i) s) +
      pathSimplex (p.periodLoop y) (affineSimplex (fun _ => stdVertices 1 j) s) = 0
  rw [affineSimplex_constant, affineSimplex_constant]
  change pathSimplex (p.periodLoop x) (stdVertices 1 i) +
    pathSimplex (p.periodLoop y) (stdVertices 1 j) = 0
  fin_cases i <;> fin_cases j <;> simp [stdVertices]

theorem periodProductSimplex_repeated_zero (p : PeriodDomain) (x y : Lattice) :
    periodProductSimplex p x y ![productCorner 0 0, productCorner 0 0] =
      ContinuousMap.const (Simplex 1) (0 : p.Torus) := by
  convert periodProductSimplex_constant p x y (n := 1) 0 0 using 2
  funext i
  fin_cases i <;> rfl

/-- The positive triangle goes first along the first period, then along the second. -/
def productTriangle01 (p : PeriodDomain) (x y : Lattice) : SingularSimplex p.Torus 2 :=
  periodProductSimplex p x y ![productCorner 0 0, productCorner 1 0, productCorner 1 1]

/-- The other nondegenerate triangle goes first along the second period. -/
def productTriangle10 (p : PeriodDomain) (x y : Lattice) : SingularSimplex p.Torus 2 :=
  periodProductSimplex p x y ![productCorner 0 0, productCorner 0 1, productCorner 1 1]

/-- The repeated-first-vertex triangle along the second period. -/
def productDegenerateLeft (p : PeriodDomain) (x y : Lattice) : SingularSimplex p.Torus 2 :=
  periodProductSimplex p x y ![productCorner 0 0, productCorner 0 0, productCorner 0 1]

/-- The repeated-first-vertex triangle along the first period. -/
def productDegenerateRight (p : PeriodDomain) (x y : Lattice) : SingularSimplex p.Torus 2 :=
  periodProductSimplex p x y ![productCorner 0 0, productCorner 0 0, productCorner 1 0]

@[simp] theorem productTriangle01_face_two (p : PeriodDomain) (x y : Lattice) :
    (productTriangle01 p x y).comp (simplexFace 1 2) = pathSimplex (p.periodLoop x) := by
  rw [productTriangle01, periodProductSimplex_face_two, periodProductSimplex_horizontal]

@[simp] theorem productTriangle01_face_zero (p : PeriodDomain) (x y : Lattice) :
    (productTriangle01 p x y).comp (simplexFace 1 0) = pathSimplex (p.periodLoop y) := by
  rw [productTriangle01, periodProductSimplex_face_zero, periodProductSimplex_vertical]

@[simp] theorem productTriangle10_face_two (p : PeriodDomain) (x y : Lattice) :
    (productTriangle10 p x y).comp (simplexFace 1 2) = pathSimplex (p.periodLoop y) := by
  rw [productTriangle10, periodProductSimplex_face_two, periodProductSimplex_vertical]

@[simp] theorem productTriangle10_face_zero (p : PeriodDomain) (x y : Lattice) :
    (productTriangle10 p x y).comp (simplexFace 1 0) = pathSimplex (p.periodLoop x) := by
  rw [productTriangle10, periodProductSimplex_face_zero, periodProductSimplex_horizontal]

@[simp] theorem productDegenerateLeft_face_two (p : PeriodDomain) (x y : Lattice) :
    (productDegenerateLeft p x y).comp (simplexFace 1 2) =
      ContinuousMap.const (Simplex 1) (0 : p.Torus) := by
  rw [productDegenerateLeft, periodProductSimplex_face_two, periodProductSimplex_repeated_zero]

@[simp] theorem productDegenerateLeft_face_zero (p : PeriodDomain) (x y : Lattice) :
    (productDegenerateLeft p x y).comp (simplexFace 1 0) = pathSimplex (p.periodLoop y) := by
  rw [productDegenerateLeft, periodProductSimplex_face_zero, periodProductSimplex_vertical]

@[simp] theorem productDegenerateRight_face_two (p : PeriodDomain) (x y : Lattice) :
    (productDegenerateRight p x y).comp (simplexFace 1 2) =
      ContinuousMap.const (Simplex 1) (0 : p.Torus) := by
  rw [productDegenerateRight, periodProductSimplex_face_two, periodProductSimplex_repeated_zero]

@[simp] theorem productDegenerateRight_face_zero (p : PeriodDomain) (x y : Lattice) :
    (productDegenerateRight p x y).comp (simplexFace 1 0) = pathSimplex (p.periodLoop x) := by
  rw [productDegenerateRight, periodProductSimplex_face_zero, periodProductSimplex_horizontal]

/-- The actual singular-chain product has precisely these four signed terms. -/
theorem periodLoop_productChain_expansion (p : PeriodDomain) (x y : Lattice) :
    inducedChain (additionMap p.Torus) 2
        (crossProductEdge p.Torus p.Torus 1
          (pathChain (p.periodLoop x)) (pathChain (p.periodLoop y))) =
      simplexChain p.Torus 2 (productTriangle01 p x y) -
        simplexChain p.Torus 2 (productDegenerateLeft p x y) -
          simplexChain p.Torus 2 (productTriangle10 p x y) +
            simplexChain p.Torus 2 (productDegenerateRight p x y) := by
  rw [pathChain, pathChain, crossProductEdge_simplex, formalEdgeCrossProduct_one_expansion]
  simp only [map_add, map_sub, productAffineChainMap_simplex, inducedChain_simplex]
  rfl

end Wikipedia.HopfProblem.PeriodTorusLineBundle.ChernCover
