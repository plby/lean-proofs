import Wikipedia.HopfProblem.SecondHurewiczSimplyConnectedTriangleSquareGeometry
import Wikipedia.HopfProblem.SecondHurewiczSimplyConnectedVertexBasic

/-!
# Boundary data of the two actual square triangles

For an arbitrary based generalized two-loop, both square triangles have
based vertices, their diagonal edges agree, and their other edges are
constant. No condition is imposed on the common diagonal itself.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.SecondHurewicz.SimplyConnected

open FirstHurewicz

variable {X : Type} [TopologicalSpace X] {x : X}

theorem lowerSquareTriangle_verticesBased (p : GenLoop (Fin 2) X x) :
    VerticesBased x 2 (p.val.comp lowerSquareTriangle) := by
  intro i
  change p (lowerSquareTriangle (stdSimplex.vertex (S := ℝ) i)) = x
  apply GenLoop.boundary p
  refine ⟨1, ?_⟩
  by_cases hi : i = 2
  · right
    apply Subtype.ext
    change (lowerSquareTriangle (stdSimplex.vertex (S := ℝ) i) 1 : ℝ) = 1
    simp [hi, stdSimplex.vertex]
  · left
    apply Subtype.ext
    change (lowerSquareTriangle (stdSimplex.vertex (S := ℝ) i) 1 : ℝ) = 0
    simp [hi, stdSimplex.vertex]

theorem upperSquareTriangle_verticesBased (p : GenLoop (Fin 2) X x) :
    VerticesBased x 2 (p.val.comp upperSquareTriangle) := by
  intro i
  change p (upperSquareTriangle (stdSimplex.vertex (S := ℝ) i)) = x
  apply GenLoop.boundary p
  refine ⟨0, ?_⟩
  by_cases hi : i = 2
  · right
    apply Subtype.ext
    change (upperSquareTriangle (stdSimplex.vertex (S := ℝ) i) 0 : ℝ) = 1
    simp [hi, stdSimplex.vertex]
  · left
    apply Subtype.ext
    change (upperSquareTriangle (stdSimplex.vertex (S := ℝ) i) 0 : ℝ) = 0
    simp [hi, stdSimplex.vertex]

/-- The two parametrizations agree on their common, possibly nonconstant, diagonal. -/
theorem squareTriangles_diagonal (p : GenLoop (Fin 2) X x) :
    (p.val.comp lowerSquareTriangle).comp (simplexFace 1 1) =
      (p.val.comp upperSquareTriangle).comp (simplexFace 1 1) := by
  apply ContinuousMap.ext
  intro s
  change p.val (lowerSquareTriangle (simplexFace 1 1 s)) =
    p.val (upperSquareTriangle (simplexFace 1 1 s))
  apply congrArg p.val
  funext i
  apply Subtype.ext
  fin_cases i
  · change (lowerSquareTriangle (simplexFace 1 1 s) 0 : ℝ) =
      (upperSquareTriangle (simplexFace 1 1 s) 0 : ℝ)
    rw [lowerSquareTriangle_zero, upperSquareTriangle_zero,
      simplexFace_apply_self, zero_add]
  · change (lowerSquareTriangle (simplexFace 1 1 s) 1 : ℝ) =
      (upperSquareTriangle (simplexFace 1 1 s) 1 : ℝ)
    rw [lowerSquareTriangle_one, upperSquareTriangle_one,
      simplexFace_apply_self, zero_add]

theorem lowerSquareTriangle_outerFace (p : GenLoop (Fin 2) X x)
    (i : Fin 3) (hi : i ≠ 1) :
    (p.val.comp lowerSquareTriangle).comp (simplexFace 1 i) =
      ContinuousMap.const (Simplex 1) x := by
  fin_cases i
  · apply ContinuousMap.ext
    intro s
    change p (lowerSquareTriangle (simplexFace 1 0 s)) = x
    apply GenLoop.boundary p
    refine ⟨0, Or.inr ?_⟩
    apply Subtype.ext
    change (lowerSquareTriangle (simplexFace 1 0 s) 0 : ℝ) = 1
    rw [lowerSquareTriangle_zero]
    have h1 : simplexFace 1 0 s 1 = s 0 := simplexFace_apply_succAbove 1 0 s 0
    have h2 : simplexFace 1 0 s 2 = s 1 := simplexFace_apply_succAbove 1 0 s 1
    rw [h1, h2]
    exact stdSimplex.add_eq_one s
  · exact (hi rfl).elim
  · apply ContinuousMap.ext
    intro s
    change p (lowerSquareTriangle (simplexFace 1 2 s)) = x
    apply GenLoop.boundary p
    refine ⟨1, Or.inl ?_⟩
    apply Subtype.ext
    change (lowerSquareTriangle (simplexFace 1 2 s) 1 : ℝ) = 0
    rw [lowerSquareTriangle_one, simplexFace_apply_self]

theorem upperSquareTriangle_outerFace (p : GenLoop (Fin 2) X x)
    (i : Fin 3) (hi : i ≠ 1) :
    (p.val.comp upperSquareTriangle).comp (simplexFace 1 i) =
      ContinuousMap.const (Simplex 1) x := by
  fin_cases i
  · apply ContinuousMap.ext
    intro s
    change p (upperSquareTriangle (simplexFace 1 0 s)) = x
    apply GenLoop.boundary p
    refine ⟨1, Or.inr ?_⟩
    apply Subtype.ext
    change (upperSquareTriangle (simplexFace 1 0 s) 1 : ℝ) = 1
    rw [upperSquareTriangle_one]
    have h1 : simplexFace 1 0 s 1 = s 0 := simplexFace_apply_succAbove 1 0 s 0
    have h2 : simplexFace 1 0 s 2 = s 1 := simplexFace_apply_succAbove 1 0 s 1
    rw [h1, h2]
    exact stdSimplex.add_eq_one s
  · exact (hi rfl).elim
  · apply ContinuousMap.ext
    intro s
    change p (upperSquareTriangle (simplexFace 1 2 s)) = x
    apply GenLoop.boundary p
    refine ⟨0, Or.inl ?_⟩
    apply Subtype.ext
    change (upperSquareTriangle (simplexFace 1 2 s) 0 : ℝ) = 0
    rw [upperSquareTriangle_zero, simplexFace_apply_self]

end Wikipedia.HopfProblem.SecondHurewicz.SimplyConnected
