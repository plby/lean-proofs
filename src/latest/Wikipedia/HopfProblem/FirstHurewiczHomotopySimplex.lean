import Wikipedia.HopfProblem.FirstHurewiczSimplex

/-!
# The two singular triangles in a path-homotopy square

The lower triangle has barycentric parametrization `(s₂,1-s₀)` and
the upper triangle has parametrization `(1-s₀,s₂)`. Their shared edge
is the diagonal. The other four edges are exactly the two paths and
the two endpoint constants of the homotopy.
-/

noncomputable section

namespace Wikipedia.HopfProblem.FirstHurewicz

def lowerTriangleMap : C(Simplex 2, unitInterval × unitInterval) where
  toFun s := (simplexCoordinate 2 2 s, unitInterval.symm (simplexCoordinate 2 0 s))
  continuous_toFun := (simplexCoordinate 2 2).continuous.prodMk
    (unitInterval.continuous_symm.comp (simplexCoordinate 2 0).continuous)

def upperTriangleMap : C(Simplex 2, unitInterval × unitInterval) where
  toFun s := (unitInterval.symm (simplexCoordinate 2 0 s), simplexCoordinate 2 2 s)
  continuous_toFun := (unitInterval.continuous_symm.comp
    (simplexCoordinate 2 0).continuous).prodMk (simplexCoordinate 2 2).continuous

theorem lowerTriangle_face_zero (s : Simplex 1) :
    lowerTriangleMap (simplexFace 1 0 s) = (simplexCoordinate 1 1 s, 1) := by
  apply Prod.ext <;> apply Subtype.ext
  · change simplexFace 1 0 s 2 = s 1
    exact congrFun (simplexFace_one_zero s) 2
  · change 1 - simplexFace 1 0 s 0 = 1
    rw [simplexFace_apply_self]
    ring

theorem lowerTriangle_face_one (s : Simplex 1) :
    lowerTriangleMap (simplexFace 1 1 s) =
      (simplexCoordinate 1 1 s, simplexCoordinate 1 1 s) := by
  apply Prod.ext <;> apply Subtype.ext
  · change simplexFace 1 1 s 2 = s 1
    exact congrFun (simplexFace_one_one s) 2
  · change 1 - simplexFace 1 1 s 0 = s 1
    have h0 : simplexFace 1 1 s 0 = s 0 := congrFun (simplexFace_one_one s) 0
    rw [h0]
    linarith [stdSimplex.add_eq_one s]

theorem lowerTriangle_face_two (s : Simplex 1) :
    lowerTriangleMap (simplexFace 1 2 s) = (0, simplexCoordinate 1 1 s) := by
  apply Prod.ext <;> apply Subtype.ext
  · change simplexFace 1 2 s 2 = 0
    exact simplexFace_apply_self 1 2 s
  · change 1 - simplexFace 1 2 s 0 = s 1
    have h0 : simplexFace 1 2 s 0 = s 0 := congrFun (simplexFace_one_two s) 0
    rw [h0]
    linarith [stdSimplex.add_eq_one s]

theorem upperTriangle_face_zero (s : Simplex 1) :
    upperTriangleMap (simplexFace 1 0 s) = (1, simplexCoordinate 1 1 s) := by
  apply Prod.ext <;> apply Subtype.ext
  · change 1 - simplexFace 1 0 s 0 = 1
    rw [simplexFace_apply_self]
    ring
  · change simplexFace 1 0 s 2 = s 1
    exact congrFun (simplexFace_one_zero s) 2

theorem upperTriangle_face_one (s : Simplex 1) :
    upperTriangleMap (simplexFace 1 1 s) =
      (simplexCoordinate 1 1 s, simplexCoordinate 1 1 s) := by
  apply Prod.ext <;> apply Subtype.ext
  · change 1 - simplexFace 1 1 s 0 = s 1
    have h0 : simplexFace 1 1 s 0 = s 0 := congrFun (simplexFace_one_one s) 0
    rw [h0]
    linarith [stdSimplex.add_eq_one s]
  · change simplexFace 1 1 s 2 = s 1
    exact congrFun (simplexFace_one_one s) 2

theorem upperTriangle_face_two (s : Simplex 1) :
    upperTriangleMap (simplexFace 1 2 s) = (simplexCoordinate 1 1 s, 0) := by
  apply Prod.ext <;> apply Subtype.ext
  · change 1 - simplexFace 1 2 s 0 = s 1
    have h0 : simplexFace 1 2 s 0 = s 0 := congrFun (simplexFace_one_two s) 0
    rw [h0]
    linarith [stdSimplex.add_eq_one s]
  · change simplexFace 1 2 s 2 = 0
    exact simplexFace_apply_self 1 2 s

variable {X : Type*} [TopologicalSpace X] {x y : X} {p q : Path x y}

def homotopyLowerSimplex (H : p.Homotopy q) : C(Simplex 2, X) :=
  H.toHomotopy.toContinuousMap.comp lowerTriangleMap

def homotopyUpperSimplex (H : p.Homotopy q) : C(Simplex 2, X) :=
  H.toHomotopy.toContinuousMap.comp upperTriangleMap

def homotopyDiagonalSimplex (H : p.Homotopy q) : C(Simplex 1, X) where
  toFun s := H (simplexCoordinate 1 1 s, simplexCoordinate 1 1 s)
  continuous_toFun := H.continuous.comp ((simplexCoordinate 1 1).continuous.prodMk
    (simplexCoordinate 1 1).continuous)

@[simp] theorem homotopyLowerSimplex_face_zero (H : p.Homotopy q) :
    (homotopyLowerSimplex H).comp (simplexFace 1 0) =
      ContinuousMap.const (Simplex 1) y := by
  apply ContinuousMap.ext
  intro s
  change H (lowerTriangleMap (simplexFace 1 0 s)) = y
  rw [lowerTriangle_face_zero, H.target]

@[simp] theorem homotopyLowerSimplex_face_one (H : p.Homotopy q) :
    (homotopyLowerSimplex H).comp (simplexFace 1 1) = homotopyDiagonalSimplex H := by
  apply ContinuousMap.ext
  intro s
  change H (lowerTriangleMap (simplexFace 1 1 s)) = _
  rw [lowerTriangle_face_one]
  rfl

@[simp] theorem homotopyLowerSimplex_face_two (H : p.Homotopy q) :
    (homotopyLowerSimplex H).comp (simplexFace 1 2) = pathSimplex p := by
  apply ContinuousMap.ext
  intro s
  change H (lowerTriangleMap (simplexFace 1 2 s)) = pathSimplex p s
  rw [lowerTriangle_face_two]
  exact H.map_zero_left _

@[simp] theorem homotopyUpperSimplex_face_zero (H : p.Homotopy q) :
    (homotopyUpperSimplex H).comp (simplexFace 1 0) = pathSimplex q := by
  apply ContinuousMap.ext
  intro s
  change H (upperTriangleMap (simplexFace 1 0 s)) = pathSimplex q s
  rw [upperTriangle_face_zero]
  exact H.map_one_left _

@[simp] theorem homotopyUpperSimplex_face_one (H : p.Homotopy q) :
    (homotopyUpperSimplex H).comp (simplexFace 1 1) = homotopyDiagonalSimplex H := by
  apply ContinuousMap.ext
  intro s
  change H (upperTriangleMap (simplexFace 1 1 s)) = _
  rw [upperTriangle_face_one]
  rfl

@[simp] theorem homotopyUpperSimplex_face_two (H : p.Homotopy q) :
    (homotopyUpperSimplex H).comp (simplexFace 1 2) =
      ContinuousMap.const (Simplex 1) x := by
  apply ContinuousMap.ext
  intro s
  change H (upperTriangleMap (simplexFace 1 2 s)) = x
  rw [upperTriangle_face_two, H.source]

end Wikipedia.HopfProblem.FirstHurewicz
