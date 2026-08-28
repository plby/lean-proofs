import Wikipedia.HopfProblem.FifthHurewiczChainsBoundaryGeometry

/-!
# Based evaluation cancels the remaining four-cube boundary

Naturality identifies every parametrized boundary face with a constant
singular-chain image. The eight faces form four opposite pairs, so their
evaluated cross products cancel already in the actual chain groups.
-/

noncomputable section

open scoped unitInterval Topology

namespace Wikipedia.HopfProblem.FifthHurewicz

open FirstHurewicz SingularMayerVietoris PeriodTorusHigherHomology

attribute [local instance] integerLinearMapModule integerTensorModule

variable {X A : Type} [TopologicalSpace X] [TopologicalSpace A]

/-- A boundary-valued parameter map has its constant evaluated edge-product image,
for parameter chains of every degree. -/
theorem evaluated_edge_boundaryMap (x : X) (a : Chains (BasedLoopSpace x) 1)
    (k : ℕ) (b : Chains A k) (f : C(A, Fin 4 → I))
    (hf : ∀ t, f t ∈ Cube.boundary (Fin 4)) :
    inducedChain (evaluation x) (k + 1)
        (crossProductEdge (BasedLoopSpace x) (Fin 4 → I) k a (inducedChain f k b)) =
      inducedChain (ContinuousMap.const (BasedLoopSpace x × A) x) (k + 1)
        (crossProductEdge (BasedLoopSpace x) A k a b) := by
  have h := crossProductEdge_natural (ContinuousMap.id (BasedLoopSpace x)) f k a b
  rw [inducedChain_id, LinearMap.id_apply] at h
  rw [← h]
  change ((inducedChain (evaluation x) (k + 1)).comp
    (inducedChain ((ContinuousMap.id (BasedLoopSpace x)).prodMap f) (k + 1))) _ = _
  rw [← inducedChain_comp, evaluation_comp_boundary x f hf]

/-- The corresponding constant image for a degree-two left factor. -/
theorem evaluated_triangle_boundaryMap (x : X) (a : Chains (BasedLoopSpace x) 2)
    (k : ℕ) (b : Chains A k) (f : C(A, Fin 4 → I))
    (hf : ∀ t, f t ∈ Cube.boundary (Fin 4)) :
    inducedChain (evaluation x) (k + 2)
        (crossProductTriangle (BasedLoopSpace x) (Fin 4 → I) k a (inducedChain f k b)) =
      inducedChain (ContinuousMap.const (BasedLoopSpace x × A) x) (k + 2)
        (crossProductTriangle (BasedLoopSpace x) A k a b) := by
  have h := crossProductTriangle_natural (ContinuousMap.id (BasedLoopSpace x)) f k a b
  rw [inducedChain_id, LinearMap.id_apply] at h
  rw [← h]
  change ((inducedChain (evaluation x) (k + 2)).comp
    (inducedChain ((ContinuousMap.id (BasedLoopSpace x)).prodMap f) (k + 2))) _ = _
  rw [← inducedChain_comp, evaluation_comp_boundary x f hf]

/-- The whole remaining four-cube boundary cancels after evaluated edge crossing. -/
theorem evaluated_edge_cubeBoundary_cancel (x : X) (a : Chains (BasedLoopSpace x) 1) :
    inducedChain (evaluation x) 4
        (crossProductEdge (BasedLoopSpace x) (Fin 4 → I) 3 a
          (((singularComplex (Fin 4 → I)).d 4 3).hom
            FourthHurewicz.fundamentalCubeChain)) = 0 := by
  have hF (t : I) (ht : t = 0 ∨ t = 1) :=
    evaluated_edge_boundaryMap x a 3 ThirdHurewicz.fundamentalCubeChain
      (remainingCubeSideFirst t) (remainingCubeSideFirst_boundary t ht)
  have hS (t : I) (ht : t = 0 ∨ t = 1) :=
    evaluated_edge_boundaryMap x a 3 ThirdHurewicz.productCubeChain
      (remainingCubeSide (FourthHurewicz.remainingCubeSideFirst t))
      (remainingCubeSide_boundary _ (FourthHurewicz.remainingCubeSideFirst_boundary t ht))
  have hL (t : I) (ht : t = 0 ∨ t = 1) :=
    evaluated_edge_boundaryMap x a 3 productThreeIntervalChain
      (remainingCubeSide (FourthHurewicz.remainingCubeSide (ThirdHurewicz.squareSideLeft t)))
      (remainingCubeSide_boundary _
        (FourthHurewicz.remainingCubeSide_boundary _ (ThirdHurewicz.squareSideLeft_boundary t ht)))
  have hR (t : I) (ht : t = 0 ∨ t = 1) :=
    evaluated_edge_boundaryMap x a 3 productThreeIntervalChain
      (remainingCubeSide (FourthHurewicz.remainingCubeSide (ThirdHurewicz.squareSideRight t)))
      (remainingCubeSide_boundary _
        (FourthHurewicz.remainingCubeSide_boundary _ (ThirdHurewicz.squareSideRight_boundary t ht)))
  simp only [remainingCubeChain_boundary, map_sub,
    hF 1 (Or.inr rfl), hF 0 (Or.inl rfl), hS 1 (Or.inr rfl), hS 0 (Or.inl rfl),
    hL 1 (Or.inr rfl), hL 0 (Or.inl rfl), hR 1 (Or.inr rfl), hR 0 (Or.inl rfl), sub_self]

/-- The same exact boundary cancellation for the homotopy and concatenation primitives. -/
theorem evaluated_triangle_cubeBoundary_cancel (x : X) (a : Chains (BasedLoopSpace x) 2) :
    inducedChain (evaluation x) 5
        (crossProductTriangle (BasedLoopSpace x) (Fin 4 → I) 3 a
          (((singularComplex (Fin 4 → I)).d 4 3).hom
            FourthHurewicz.fundamentalCubeChain)) = 0 := by
  have hF (t : I) (ht : t = 0 ∨ t = 1) :=
    evaluated_triangle_boundaryMap x a 3 ThirdHurewicz.fundamentalCubeChain
      (remainingCubeSideFirst t) (remainingCubeSideFirst_boundary t ht)
  have hS (t : I) (ht : t = 0 ∨ t = 1) :=
    evaluated_triangle_boundaryMap x a 3 ThirdHurewicz.productCubeChain
      (remainingCubeSide (FourthHurewicz.remainingCubeSideFirst t))
      (remainingCubeSide_boundary _ (FourthHurewicz.remainingCubeSideFirst_boundary t ht))
  have hL (t : I) (ht : t = 0 ∨ t = 1) :=
    evaluated_triangle_boundaryMap x a 3 productThreeIntervalChain
      (remainingCubeSide (FourthHurewicz.remainingCubeSide (ThirdHurewicz.squareSideLeft t)))
      (remainingCubeSide_boundary _
        (FourthHurewicz.remainingCubeSide_boundary _ (ThirdHurewicz.squareSideLeft_boundary t ht)))
  have hR (t : I) (ht : t = 0 ∨ t = 1) :=
    evaluated_triangle_boundaryMap x a 3 productThreeIntervalChain
      (remainingCubeSide (FourthHurewicz.remainingCubeSide (ThirdHurewicz.squareSideRight t)))
      (remainingCubeSide_boundary _
        (FourthHurewicz.remainingCubeSide_boundary _ (ThirdHurewicz.squareSideRight_boundary t ht)))
  simp only [remainingCubeChain_boundary, map_sub,
    hF 1 (Or.inr rfl), hF 0 (Or.inl rfl), hS 1 (Or.inr rfl), hS 0 (Or.inl rfl),
    hL 1 (Or.inr rfl), hL 0 (Or.inl rfl), hR 1 (Or.inr rfl), hR 0 (Or.inl rfl), sub_self]

end Wikipedia.HopfProblem.FifthHurewicz
