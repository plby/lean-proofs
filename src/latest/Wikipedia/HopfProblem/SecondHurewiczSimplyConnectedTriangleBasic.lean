import Wikipedia.HopfProblem.SecondHurewicz

/-!
# Native second homotopy classes of based singular triangles

The piecewise-affine quotient of the square collapses its upper triangle
onto the edge joining vertices zero and two. The lower triangle is mapped
with its original positive orientation. Composing with a singular triangle
which is constant on its whole boundary gives a genuine generalized loop.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.SecondHurewicz.SimplyConnected

open FirstHurewicz SingularMayerVietoris

/-- The entire boundary of the actual standard triangle. -/
def triangleBoundary : Set (Simplex 2) := {s | ∃ i, s i = 0}

/-- Based triangles retain their actual continuous singular-simplex maps. -/
def BasedTriangle {X : Type} [TopologicalSpace X] (x : X) :=
  {τ : C(Simplex 2, X) // ∀ s ∈ triangleBoundary, τ s = x}

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] {x : X}

/-- The PL square-to-triangle quotient, with positive orientation on the
lower half and the upper half collapsed into the opposite edge. -/
def triangleQuotient : C(I × I, Simplex 2) where
  toFun z := ⟨![1 - (z.1 : ℝ), (z.1 : ℝ) - min (z.1 : ℝ) (z.2 : ℝ),
    min (z.1 : ℝ) (z.2 : ℝ)], by
      constructor
      · intro i
        fin_cases i
        · exact sub_nonneg.mpr z.1.property.2
        · exact sub_nonneg.mpr (min_le_left _ _)
        · exact le_min z.1.property.1 z.2.property.1
      · simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero,
          Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_fin_one]
        ring⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    fin_cases i <;> dsimp <;> fun_prop

@[simp] theorem triangleQuotient_zero (z : I × I) :
    triangleQuotient z 0 = 1 - (z.1 : ℝ) := rfl

@[simp] theorem triangleQuotient_one (z : I × I) :
    triangleQuotient z 1 = (z.1 : ℝ) - min (z.1 : ℝ) (z.2 : ℝ) := rfl

@[simp] theorem triangleQuotient_two (z : I × I) :
    triangleQuotient z 2 = min (z.1 : ℝ) (z.2 : ℝ) := rfl

/-- The same quotient on Mathlib's literal two-dimensional cube. -/
def triangleCubeQuotient : C(Fin 2 → I, Simplex 2) :=
  triangleQuotient.comp ⟨fun t => (t 0, t 1), by fun_prop⟩

@[simp] theorem triangleCubeQuotient_apply (t : Fin 2 → I) :
    triangleCubeQuotient t = triangleQuotient (t 0, t 1) := rfl

theorem triangleCubeQuotient_boundary (t : Fin 2 → I)
    (ht : t ∈ Cube.boundary (Fin 2)) : triangleCubeQuotient t ∈ triangleBoundary := by
  rcases ht with ⟨i, hi | hi⟩
  · fin_cases i
    · refine ⟨2, ?_⟩
      change t 0 = 0 at hi
      change min (t 0 : ℝ) (t 1 : ℝ) = 0
      simp [hi, min_eq_left (t 1).property.1]
    · refine ⟨2, ?_⟩
      change t 1 = 0 at hi
      change min (t 0 : ℝ) (t 1 : ℝ) = 0
      simp [hi, min_eq_right (t 0).property.1]
  · fin_cases i
    · refine ⟨0, ?_⟩
      change t 0 = 1 at hi
      change 1 - (t 0 : ℝ) = 0
      simp [hi]
    · refine ⟨1, ?_⟩
      change t 1 = 1 at hi
      change (t 0 : ℝ) - min (t 0 : ℝ) (t 1 : ℝ) = 0
      simp [hi, min_eq_left (t 0).property.2]

/-- The native generalized loop represented by a based singular triangle. -/
def basedTriangleLoop (τ : BasedTriangle x) : GenLoop (Fin 2) X x :=
  ⟨τ.val.comp triangleCubeQuotient,
    fun t ht => τ.property _ (triangleCubeQuotient_boundary t ht)⟩

@[simp] theorem basedTriangleLoop_apply (τ : BasedTriangle x) (t : Fin 2 → I) :
    basedTriangleLoop τ t = τ.val (triangleQuotient (t 0, t 1)) := rfl

theorem squareMap_basedTriangleLoop (τ : BasedTriangle x) :
    squareMap (basedTriangleLoop τ) = τ.val.comp triangleQuotient := by
  ext z
  change τ.val (triangleQuotient (squareCoordinates z 0, squareCoordinates z 1)) = _
  rw [squareCoordinates_zero, squareCoordinates_one]
  rfl

/-- The class in the actual native second homotopy group, in additive notation. -/
def basedTriangleClass (τ : BasedTriangle x) : Additive (π_ 2 X x) :=
  Additive.ofMul (⟦basedTriangleLoop τ⟧ : π_ 2 X x)

/-- Every actual face of a based triangle is the constant singular edge. -/
theorem basedTriangle_face (τ : BasedTriangle x) (i : Fin 3) :
    τ.val.comp (simplexFace 1 i) = ContinuousMap.const (Simplex 1) x := by
  ext s
  exact τ.property _ ⟨i, simplexFace_apply_self 1 i s⟩

/-- Constant triangles are based without further topological assumptions. -/
def constantBasedTriangle (x : X) : BasedTriangle x :=
  ⟨ContinuousMap.const (Simplex 2) x, fun _ _ => rfl⟩

@[simp] theorem basedTriangleLoop_constant (x : X) :
    basedTriangleLoop (constantBasedTriangle x) = GenLoop.const := rfl

@[simp] theorem basedTriangleClass_constant (x : X) :
    basedTriangleClass (constantBasedTriangle x) = 0 := rfl

/-- Continuous postcomposition preserves based triangles. -/
def mapBasedTriangle (f : C(X, Y)) (τ : BasedTriangle x) : BasedTriangle (f x) :=
  ⟨f.comp τ.val, fun s hs => congrArg f (τ.property s hs)⟩

@[simp] theorem basedTriangleLoop_map (f : C(X, Y)) (τ : BasedTriangle x) :
    basedTriangleLoop (mapBasedTriangle f τ) = mapGenLoop f x (basedTriangleLoop τ) := rfl

end Wikipedia.HopfProblem.SecondHurewicz.SimplyConnected
