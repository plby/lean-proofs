import Wikipedia.HopfProblem.ThirdHurewiczEvaluation

/-!
# Cancellation of the square boundary under based evaluation

The actual fundamental square has four oriented edges. After crossing
with a chain in the based two-loop space, evaluation sends every one of
these sides to the same constant singular-chain image. Their signs
therefore cancel before passing to homology.
-/

noncomputable section

open scoped unitInterval Topology

namespace Wikipedia.HopfProblem.ThirdHurewicz

open FirstHurewicz SingularMayerVietoris PeriodTorusHigherHomology

attribute [local instance] integerLinearMapModule integerTensorModule

/-- A side with the first remaining coordinate fixed. -/
def squareSideLeft (t : I) : C(I, Fin 2 → I) :=
  SecondHurewicz.squareCoordinates.comp (crossInsertLeft t)

/-- A side with the second remaining coordinate fixed. -/
def squareSideRight (t : I) : C(I, Fin 2 → I) :=
  SecondHurewicz.squareCoordinates.comp (crossInsertRight t)

theorem squareSideLeft_boundary (t : I) (ht : t = 0 ∨ t = 1) (s : I) :
    squareSideLeft t s ∈ Cube.boundary (Fin 2) := by
  refine ⟨0, ?_⟩
  change SecondHurewicz.squareCoordinates (t, s) 0 = 0 ∨
    SecondHurewicz.squareCoordinates (t, s) 0 = 1
  simpa only [SecondHurewicz.squareCoordinates_zero] using ht

theorem squareSideRight_boundary (t : I) (ht : t = 0 ∨ t = 1) (s : I) :
    squareSideRight t s ∈ Cube.boundary (Fin 2) := by
  refine ⟨1, ?_⟩
  change SecondHurewicz.squareCoordinates (s, t) 1 = 0 ∨
    SecondHurewicz.squareCoordinates (s, t) 1 = 1
  simpa only [SecondHurewicz.squareCoordinates_one] using ht

/-- The boundary of the frozen fundamental chain in the native square. -/
theorem fundamentalSquareChain_boundary :
    boundaryTwo (Fin 2 → I) SecondHurewicz.fundamentalSquareChain =
      inducedChain (squareSideLeft 1) 1 SecondHurewicz.intervalChain -
        inducedChain (squareSideLeft 0) 1 SecondHurewicz.intervalChain -
        (inducedChain (squareSideRight 1) 1 SecondHurewicz.intervalChain -
          inducedChain (squareSideRight 0) 1 SecondHurewicz.intervalChain) := by
  change ((singularComplex (Fin 2 → I)).d 2 1).hom
    (inducedChain SecondHurewicz.squareCoordinates 2 SecondHurewicz.productSquareChain) = _
  rw [← inducedChain_boundary]
  change inducedChain SecondHurewicz.squareCoordinates 1
    (boundaryTwo (I × I) SecondHurewicz.productSquareChain) = _
  rw [SecondHurewicz.productSquareChain_boundary]
  simp only [map_sub, squareSideLeft, squareSideRight,
    inducedChain_comp, LinearMap.comp_apply]

variable {X : Type} [TopologicalSpace X]

/-- All boundary-edge factors have the same actual evaluated two-chain. -/
theorem evaluated_edge_boundaryMap (x : X) (a : Chains (BasedLoopSpace x) 1)
    (f : C(I, Fin 2 → I)) (hf : ∀ t, f t ∈ Cube.boundary (Fin 2)) :
    inducedChain (evaluation x) 2
        (crossProductEdge (BasedLoopSpace x) (Fin 2 → I) 1 a
          (inducedChain f 1 SecondHurewicz.intervalChain)) =
      inducedChain (ContinuousMap.const (BasedLoopSpace x × I) x) 2
        (crossProductEdge (BasedLoopSpace x) I 1 a SecondHurewicz.intervalChain) := by
  have h := crossProductEdge_natural (ContinuousMap.id (BasedLoopSpace x)) f 1
    a SecondHurewicz.intervalChain
  rw [inducedChain_id, LinearMap.id_apply] at h
  rw [← h]
  change ((inducedChain (evaluation x) 2).comp
    (inducedChain ((ContinuousMap.id (BasedLoopSpace x)).prodMap f) 2)) _ = _
  rw [← inducedChain_comp, evaluation_comp_boundary x f hf]

/-- The same boundary-edge fact for a degree-two left chain. -/
theorem evaluated_triangle_boundaryMap (x : X) (a : Chains (BasedLoopSpace x) 2)
    (f : C(I, Fin 2 → I)) (hf : ∀ t, f t ∈ Cube.boundary (Fin 2)) :
    inducedChain (evaluation x) 3
        (crossProductTriangle (BasedLoopSpace x) (Fin 2 → I) 1 a
          (inducedChain f 1 SecondHurewicz.intervalChain)) =
      inducedChain (ContinuousMap.const (BasedLoopSpace x × I) x) 3
        (crossProductTriangle (BasedLoopSpace x) I 1 a SecondHurewicz.intervalChain) := by
  have h := crossProductTriangle_natural (ContinuousMap.id (BasedLoopSpace x)) f 1
    a SecondHurewicz.intervalChain
  rw [inducedChain_id, LinearMap.id_apply] at h
  rw [← h]
  change ((inducedChain (evaluation x) 3).comp
    (inducedChain ((ContinuousMap.id (BasedLoopSpace x)).prodMap f) 3)) _ = _
  rw [← inducedChain_comp, evaluation_comp_boundary x f hf]

/-- The evaluated square-boundary term vanishes as an actual two-chain. -/
theorem evaluated_edge_squareBoundary_cancel (x : X) (a : Chains (BasedLoopSpace x) 1) :
    inducedChain (evaluation x) 2
        (crossProductEdge (BasedLoopSpace x) (Fin 2 → I) 1 a
          (boundaryTwo (Fin 2 → I) SecondHurewicz.fundamentalSquareChain)) = 0 := by
  have hL (t : I) (ht : t = 0 ∨ t = 1) :=
    evaluated_edge_boundaryMap x a (squareSideLeft t) (squareSideLeft_boundary t ht)
  have hR (t : I) (ht : t = 0 ∨ t = 1) :=
    evaluated_edge_boundaryMap x a (squareSideRight t) (squareSideRight_boundary t ht)
  simp only [fundamentalSquareChain_boundary, map_sub,
    hL 1 (Or.inr rfl), hL 0 (Or.inl rfl), hR 1 (Or.inr rfl), hR 0 (Or.inl rfl), sub_self]

/-- The evaluated square-boundary term vanishes as an actual three-chain. -/
theorem evaluated_triangle_squareBoundary_cancel (x : X)
    (a : Chains (BasedLoopSpace x) 2) :
    inducedChain (evaluation x) 3
        (crossProductTriangle (BasedLoopSpace x) (Fin 2 → I) 1 a
          (boundaryTwo (Fin 2 → I) SecondHurewicz.fundamentalSquareChain)) = 0 := by
  have hL (t : I) (ht : t = 0 ∨ t = 1) :=
    evaluated_triangle_boundaryMap x a (squareSideLeft t) (squareSideLeft_boundary t ht)
  have hR (t : I) (ht : t = 0 ∨ t = 1) :=
    evaluated_triangle_boundaryMap x a (squareSideRight t) (squareSideRight_boundary t ht)
  simp only [fundamentalSquareChain_boundary, map_sub,
    hL 1 (Or.inr rfl), hL 0 (Or.inl rfl), hR 1 (Or.inr rfl), hR 0 (Or.inl rfl), sub_self]

end Wikipedia.HopfProblem.ThirdHurewicz
