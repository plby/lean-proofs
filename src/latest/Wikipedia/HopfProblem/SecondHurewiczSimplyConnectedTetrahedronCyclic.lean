import Wikipedia.HopfProblem.SecondHurewiczSimplyConnectedTetrahedronBasic
import Wikipedia.HopfProblem.SecondHurewiczSimplyConnectedTetrahedronRotation

/-!
# Cyclic triangle coordinates and a genuine relative square homotopy

A cyclic change of the triangle vertices agrees, up to a boundary-preserving
affine interpolation, with a quarter-turn of its square quotient. No
homological detection theorem is used here.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.SecondHurewicz.SimplyConnected

open FirstHurewicz

/-- An orientation-preserving cyclic permutation of triangle vertices. -/
def triangleCyclicPermutation : C(Simplex 2, Simplex 2) where
  toFun s := ⟨![s 1, s 2, s 0], by
    constructor
    · intro i
      fin_cases i <;> exact stdSimplex.zero_le s _
    · have hs := stdSimplex.sum_eq_one s
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero,
        Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_fin_one] at hs ⊢
      change s 0 + (s 1 + s 2) = 1 at hs
      linarith⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    fin_cases i
    · exact (continuous_apply 1).comp continuous_subtype_val
    · exact (continuous_apply 2).comp continuous_subtype_val
    · exact (continuous_apply 0).comp continuous_subtype_val

@[simp] theorem triangleCyclicPermutation_zero (s : Simplex 2) :
    triangleCyclicPermutation s 0 = s 1 := rfl

@[simp] theorem triangleCyclicPermutation_one (s : Simplex 2) :
    triangleCyclicPermutation s 1 = s 2 := rfl

@[simp] theorem triangleCyclicPermutation_two (s : Simplex 2) :
    triangleCyclicPermutation s 2 = s 0 := rfl

theorem triangleCyclicPermutation_boundary (s : Simplex 2)
    (hs : s ∈ triangleBoundary) : triangleCyclicPermutation s ∈ triangleBoundary := by
  obtain ⟨i, hi⟩ := hs
  fin_cases i
  · exact ⟨2, hi⟩
  · exact ⟨0, hi⟩
  · exact ⟨1, hi⟩

variable {X : Type} [TopologicalSpace X] {x : X}

/-- The same based triangle with its vertices cyclically permuted. -/
def cyclicBasedTriangle (τ : BasedTriangle x) : BasedTriangle x :=
  ⟨τ.val.comp triangleCyclicPermutation,
    fun s hs => τ.property _ (triangleCyclicPermutation_boundary s hs)⟩

@[simp] theorem cyclicBasedTriangle_apply (τ : BasedTriangle x) (s : Simplex 2) :
    (cyclicBasedTriangle τ).val s = τ.val (triangleCyclicPermutation s) := rfl

/-- On each side, the two parametrizations lie on a common actual triangle edge. -/
theorem cyclicTriangleQuotient_commonZero (u : Fin 2 → I)
    (hu : u ∈ Cube.boundary (Fin 2)) :
    ∃ i : Fin 3,
      triangleCyclicPermutation (triangleCubeQuotient u) i = 0 ∧
        triangleCubeQuotient (quarterTurn u) i = 0 := by
  rcases hu with ⟨i, hi | hi⟩
  · fin_cases i
    · change u 0 = 0 at hi
      refine ⟨1, ?_, ?_⟩ <;>
        simp [hi, min_eq_left (u 1).property.1, min_eq_left (u 1).property.2]
    · change u 1 = 0 at hi
      refine ⟨1, ?_, ?_⟩
      · simp [hi, min_eq_right (u 0).property.1]
      · simp [hi, (u 0).property.2]
  · fin_cases i
    · change u 0 = 1 at hi
      refine ⟨2, ?_, ?_⟩ <;>
        simp [hi, min_eq_right (u 1).property.1]
    · change u 1 = 1 at hi
      refine ⟨0, ?_, ?_⟩ <;>
        simp [hi, min_eq_left (u 0).property.2]

theorem cyclicTriangleQuotient_blend_boundary (t : I) (u : Fin 2 → I)
    (hu : u ∈ Cube.boundary (Fin 2)) :
    tetrahedronSimplexBlend t
      (triangleCyclicPermutation (triangleCubeQuotient u))
      (triangleCubeQuotient (quarterTurn u)) ∈ triangleBoundary := by
  obtain ⟨i, hi, hj⟩ := cyclicTriangleQuotient_commonZero u hu
  exact ⟨i, tetrahedronSimplexBlend_zero_coordinate t _ _ i hi hj⟩

/-- The relative homotopy retains the original singular triangle map. -/
def cyclicTriangleLoopHomotopy (τ : BasedTriangle x) :
    (basedTriangleLoop (cyclicBasedTriangle τ)).val.HomotopyRel
      (rotatedSquareLoop (basedTriangleLoop τ)).val (Cube.boundary (Fin 2)) where
  toFun p := τ.val (tetrahedronSimplexBlend p.1
    (triangleCyclicPermutation (triangleCubeQuotient p.2))
    (triangleCubeQuotient (quarterTurn p.2)))
  continuous_toFun := τ.val.continuous.comp
    (tetrahedronSimplexBlendMap (triangleCyclicPermutation.comp triangleCubeQuotient)
      (triangleCubeQuotient.comp quarterTurn)).continuous
  map_zero_left u := by
    change τ.val (tetrahedronSimplexBlend 0 _ _) =
      τ.val (triangleCyclicPermutation (triangleCubeQuotient u))
    rw [tetrahedronSimplexBlend_zero]
  map_one_left u := by
    change τ.val (tetrahedronSimplexBlend 1 _ _) =
      τ.val (triangleCubeQuotient (quarterTurn u))
    rw [tetrahedronSimplexBlend_one]
  prop' t u hu :=
    (τ.property _ (cyclicTriangleQuotient_blend_boundary t u hu)).trans
      ((basedTriangleLoop (cyclicBasedTriangle τ)).property u hu).symm

/-- The cyclic permutation preserves the actual native second homotopy class. -/
@[simp] theorem basedTriangleClass_cyclic (τ : BasedTriangle x) :
    basedTriangleClass (cyclicBasedTriangle τ) = basedTriangleClass τ := by
  have h : GenLoop.Homotopic (basedTriangleLoop (cyclicBasedTriangle τ))
      (rotatedSquareLoop (basedTriangleLoop τ)) := ⟨cyclicTriangleLoopHomotopy τ⟩
  have he : (⟦basedTriangleLoop (cyclicBasedTriangle τ)⟧ : π_ 2 X x) =
      ⟦rotatedSquareLoop (basedTriangleLoop τ)⟧ := Quotient.sound h
  exact congrArg Additive.ofMul
    (he.trans (rotatedSquareLoop_class (basedTriangleLoop τ)))

end Wikipedia.HopfProblem.SecondHurewicz.SimplyConnected
