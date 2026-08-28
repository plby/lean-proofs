import Wikipedia.HopfProblem.PeriodTorusLineBundleChernTriangleFrame
import Wikipedia.HopfProblem.PeriodTorusLineBundleChernClass

/-!
# The Chern obstruction in the actual whole-simplex native frame

The genuine native boundary loop is expressed in the already constructed
nonzero frame on the whole singular triangle.  Applying the inverse of
that actual fibre-linear equivalence gives a continuous punctured-plane
loop.  It is proved equal to the previously computed scalar loop, so the
Chern cochain really is the winding of the native section in its native
frame, rather than an assigned scalar model.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusLineBundle.Chern

open PeriodTorusAppellHumbert ChernCover FirstHurewicz Bundle

variable {p : PeriodDomain} (F : FactorOfAutomorphy p)

/-- The literal parameter edge from vertex zero to vertex one. -/
abbrev triangleParameterEdge01 :
    Path (stdSimplex.vertex (S := ℝ) (0 : Fin 3)) (stdSimplex.vertex (1 : Fin 3)) :=
  triangleEdge01 (ContinuousMap.id (Simplex 2))

/-- The literal parameter edge from vertex one to vertex two. -/
abbrev triangleParameterEdge12 :
    Path (stdSimplex.vertex (S := ℝ) (1 : Fin 3)) (stdSimplex.vertex (2 : Fin 3)) :=
  triangleEdge12 (ContinuousMap.id (Simplex 2))

/-- The literal parameter edge from vertex zero to vertex two. -/
abbrev triangleParameterEdge02 :
    Path (stdSimplex.vertex (S := ℝ) (0 : Fin 3)) (stdSimplex.vertex (2 : Fin 3)) :=
  triangleEdge02 (ContinuousMap.id (Simplex 2))

/-- The positive boundary parameter of the actual standard two-simplex: `01,12,20`. -/
def triangleBoundaryParameter :
    Path (stdSimplex.vertex (S := ℝ) (0 : Fin 3)) (stdSimplex.vertex (0 : Fin 3)) :=
  (triangleParameterEdge01.trans triangleParameterEdge12).trans triangleParameterEdge02.symm

/-- The boundary lift is the restriction of one actual frame-producing simplex lift. -/
theorem triangleBoundaryLift_eq_simplexLift (σ : SingularSimplex p.Torus 2)
    (t : unitInterval) :
    triangleBoundaryLift σ t = simplexLift p σ (triangleBoundaryParameter t) := by
  simp only [triangleBoundaryLift, triangleBoundaryParameter, Path.trans_apply]
  split_ifs <;> rfl

/-- The original native boundary vectors are given by the actual whole-simplex coordinate map. -/
theorem nativeTriangleBoundaryLoop_coordinateMap (σ : SingularSimplex p.Torus 2)
    (t : unitInterval) :
    nativeTriangleBoundaryLoop F σ t = nativeSimplexCoordinateMap F σ
      (triangleBoundaryParameter t, (nativeTriangleScalarLoop F σ t : ℂ)) := by
  rw [nativeTriangleBoundaryLoop_coordinates, triangleBoundaryLift_eq_simplexLift]
  rfl

/-- In the native bundle this is literal scalar multiplication of the true whole-triangle frame. -/
theorem nativeTriangleBoundaryLoop_in_frame (σ : SingularSimplex p.Torus 2)
    (t : unitInterval) :
    nativeTriangleBoundaryLoop F σ t =
      ⟨σ (triangleBoundaryParameter t),
        (nativeTriangleScalarLoop F σ t : ℂ) •
          nativeSimplexFrame F σ (triangleBoundaryParameter t)⟩ := by
  rw [nativeTriangleBoundaryLoop_coordinateMap, nativeSimplexCoordinateMap_eq_smul_frame]

/-- The coefficient is uniquely determined by the actual native boundary vector. -/
theorem nativeTriangleBoundaryLoop_coordinate_unique (σ : SingularSimplex p.Torus 2)
    (t : unitInterval) (c : ℂ) :
    nativeSimplexCoordinateMap F σ (triangleBoundaryParameter t, c) =
      nativeTriangleBoundaryLoop F σ t ↔ c = (nativeTriangleScalarLoop F σ t : ℂ) := by
  rw [nativeTriangleBoundaryLoop_coordinateMap, nativeSimplexCoordinateMap_eq,
    nativeSimplexCoordinateMap_eq]
  constructor
  · intro h
    apply (nativeSimplexFiberEquiv F σ (triangleBoundaryParameter t)).injective
    exact Bundle.TotalSpace.mk_injective _ h
  · rintro rfl
    rfl

/-- Apply the inverse actual native fibre coordinate to the actual boundary-section vector. -/
def nativeBoundaryFrameCoordinate (σ : SingularSimplex p.Torus 2) (t : unitInterval) : ℂ :=
  (nativeSimplexFiberEquiv F σ (triangleBoundaryParameter t)).symm
    (nativeTriangleBoundaryLoop F σ t).2

theorem nativeBoundaryFrameCoordinate_eq (σ : SingularSimplex p.Torus 2)
    (t : unitInterval) :
    nativeBoundaryFrameCoordinate F σ t = (nativeTriangleScalarLoop F σ t : ℂ) := by
  unfold nativeBoundaryFrameCoordinate
  rw [nativeTriangleBoundaryLoop_coordinateMap, nativeSimplexCoordinateMap_fiber,
    LinearEquiv.symm_apply_apply]

/-- The actual inverse-frame coordinates form a genuine based punctured-plane loop. -/
def nativeBoundaryFrameLoop (σ : SingularSimplex p.Torus 2) : BasedLoop where
  toFun t := ⟨nativeBoundaryFrameCoordinate F σ t, by
    rw [nativeBoundaryFrameCoordinate_eq]
    exact (nativeTriangleScalarLoop F σ t).property⟩
  continuous_toFun := by
    convert (nativeTriangleScalarLoop F σ).continuous using 1
    funext t
    apply Subtype.ext
    exact nativeBoundaryFrameCoordinate_eq F σ t
  source' := by
    apply Subtype.ext
    change nativeBoundaryFrameCoordinate F σ 0 = 1
    rw [nativeBoundaryFrameCoordinate_eq]
    exact congrArg Subtype.val (nativeTriangleScalarLoop F σ).source
  target' := by
    apply Subtype.ext
    change nativeBoundaryFrameCoordinate F σ 1 = 1
    rw [nativeBoundaryFrameCoordinate_eq]
    exact congrArg Subtype.val (nativeTriangleScalarLoop F σ).target

theorem nativeBoundaryFrameLoop_eq (σ : SingularSimplex p.Torus 2) :
    nativeBoundaryFrameLoop F σ = nativeTriangleScalarLoop F σ := by
  apply Path.ext
  funext t
  exact Subtype.ext (nativeBoundaryFrameCoordinate_eq F σ t)

/-- The integral obstruction is the winding of the unique genuine inverse-frame coordinates. -/
theorem triangleObstruction_eq_winding_nativeFrame (σ : SingularSimplex p.Torus 2) :
    triangleObstruction F σ = windingNumber (nativeBoundaryFrameLoop F σ) := by
  rw [nativeBoundaryFrameLoop_eq]
  rfl

/-- The native singular Chern cochain has precisely this actual frame-obstruction value. -/
theorem firstChernCochain_simplex_eq_winding_nativeFrame (σ : SingularSimplex p.Torus 2) :
    firstChernCochain F (simplexChain p.Torus 2 σ) =
      windingNumber (nativeBoundaryFrameLoop F σ) := by
  rw [firstChernCochain_simplex, nativeBoundaryFrameLoop_eq]

end Wikipedia.HopfProblem.PeriodTorusLineBundle.Chern
