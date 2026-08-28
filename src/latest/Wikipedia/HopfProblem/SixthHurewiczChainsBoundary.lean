import Wikipedia.HopfProblem.SixthHurewiczChainsBoundaryGeometry

/-!
# Based evaluation cancels the remaining five-cube boundary

Naturality identifies every parametrized boundary face with a constant
singular-chain image. The ten faces form five opposite pairs, so their
evaluated cross products cancel already in the actual chain groups.
-/

noncomputable section

open scoped unitInterval Topology

namespace Wikipedia.HopfProblem.SixthHurewicz

open FirstHurewicz SingularMayerVietoris PeriodTorusHigherHomology

attribute [local instance] integerLinearMapModule integerTensorModule

variable {X A : Type} [TopologicalSpace X] [TopologicalSpace A]

/-- A boundary-valued parameter map has its constant evaluated edge-product image,
for parameter chains of every degree. -/
theorem evaluated_edge_boundaryMap (x : X) (a : Chains (BasedLoopSpace x) 1)
    (k : ℕ) (b : Chains A k) (f : C(A, Fin 5 → I))
    (hf : ∀ t, f t ∈ Cube.boundary (Fin 5)) :
    inducedChain (evaluation x) (k + 1)
        (crossProductEdge (BasedLoopSpace x) (Fin 5 → I) k a (inducedChain f k b)) =
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
    (k : ℕ) (b : Chains A k) (f : C(A, Fin 5 → I))
    (hf : ∀ t, f t ∈ Cube.boundary (Fin 5)) :
    inducedChain (evaluation x) (k + 2)
        (crossProductTriangle (BasedLoopSpace x) (Fin 5 → I) k a (inducedChain f k b)) =
      inducedChain (ContinuousMap.const (BasedLoopSpace x × A) x) (k + 2)
        (crossProductTriangle (BasedLoopSpace x) A k a b) := by
  have h := crossProductTriangle_natural (ContinuousMap.id (BasedLoopSpace x)) f k a b
  rw [inducedChain_id, LinearMap.id_apply] at h
  rw [← h]
  change ((inducedChain (evaluation x) (k + 2)).comp
    (inducedChain ((ContinuousMap.id (BasedLoopSpace x)).prodMap f) (k + 2))) _ = _
  rw [← inducedChain_comp, evaluation_comp_boundary x f hf]

/-- The whole remaining five-cube boundary cancels after evaluated edge crossing. -/
theorem evaluated_edge_cubeBoundary_cancel (x : X) (a : Chains (BasedLoopSpace x) 1) :
    inducedChain (evaluation x) 5
        (crossProductEdge (BasedLoopSpace x) (Fin 5 → I) 4 a
          (((singularComplex (Fin 5 → I)).d 5 4).hom
            FifthHurewicz.fundamentalCubeChain)) = 0 := by
  have hF (t : I) (ht : t = 0 ∨ t = 1) :=
    evaluated_edge_boundaryMap x a 4 FourthHurewicz.fundamentalCubeChain
      (remainingCubeSideFirst t) (remainingCubeSideFirst_boundary t ht)
  have hS (t : I) (ht : t = 0 ∨ t = 1) :=
    evaluated_edge_boundaryMap x a 4 FourthHurewicz.productCubeChain
      (remainingCubeSide (FifthHurewicz.remainingCubeSideFirst t))
      (remainingCubeSide_boundary _ (FifthHurewicz.remainingCubeSideFirst_boundary t ht))
  have hT (t : I) (ht : t = 0 ∨ t = 1) :=
    evaluated_edge_boundaryMap x a 4 productTwoIntervalSquareChain
      (remainingCubeSide
        (FifthHurewicz.remainingCubeSide (FourthHurewicz.remainingCubeSideFirst t)))
      (remainingCubeSide_boundary _
        (FifthHurewicz.remainingCubeSide_boundary _
          (FourthHurewicz.remainingCubeSideFirst_boundary t ht)))
  have hL (t : I) (ht : t = 0 ∨ t = 1) :=
    evaluated_edge_boundaryMap x a 4 productFourIntervalChain
      (remainingCubeSide (FifthHurewicz.remainingCubeSide
        (FourthHurewicz.remainingCubeSide (ThirdHurewicz.squareSideLeft t))))
      (remainingCubeSide_boundary _ (FifthHurewicz.remainingCubeSide_boundary _
        (FourthHurewicz.remainingCubeSide_boundary _
          (ThirdHurewicz.squareSideLeft_boundary t ht))))
  have hR (t : I) (ht : t = 0 ∨ t = 1) :=
    evaluated_edge_boundaryMap x a 4 productFourIntervalChain
      (remainingCubeSide (FifthHurewicz.remainingCubeSide
        (FourthHurewicz.remainingCubeSide (ThirdHurewicz.squareSideRight t))))
      (remainingCubeSide_boundary _ (FifthHurewicz.remainingCubeSide_boundary _
        (FourthHurewicz.remainingCubeSide_boundary _
          (ThirdHurewicz.squareSideRight_boundary t ht))))
  simp only [remainingCubeChain_boundary, map_sub,
    hF 1 (Or.inr rfl), hF 0 (Or.inl rfl), hS 1 (Or.inr rfl), hS 0 (Or.inl rfl),
    hT 1 (Or.inr rfl), hT 0 (Or.inl rfl),
    hL 1 (Or.inr rfl), hL 0 (Or.inl rfl), hR 1 (Or.inr rfl), hR 0 (Or.inl rfl), sub_self]

/-- The whole remaining five-cube boundary cancels after evaluated triangle crossing. -/
theorem evaluated_triangle_cubeBoundary_cancel (x : X) (a : Chains (BasedLoopSpace x) 2) :
    inducedChain (evaluation x) 6
        (crossProductTriangle (BasedLoopSpace x) (Fin 5 → I) 4 a
          (((singularComplex (Fin 5 → I)).d 5 4).hom
            FifthHurewicz.fundamentalCubeChain)) = 0 := by
  have hF (t : I) (ht : t = 0 ∨ t = 1) :=
    evaluated_triangle_boundaryMap x a 4 FourthHurewicz.fundamentalCubeChain
      (remainingCubeSideFirst t) (remainingCubeSideFirst_boundary t ht)
  have hS (t : I) (ht : t = 0 ∨ t = 1) :=
    evaluated_triangle_boundaryMap x a 4 FourthHurewicz.productCubeChain
      (remainingCubeSide (FifthHurewicz.remainingCubeSideFirst t))
      (remainingCubeSide_boundary _ (FifthHurewicz.remainingCubeSideFirst_boundary t ht))
  have hT (t : I) (ht : t = 0 ∨ t = 1) :=
    evaluated_triangle_boundaryMap x a 4 productTwoIntervalSquareChain
      (remainingCubeSide
        (FifthHurewicz.remainingCubeSide (FourthHurewicz.remainingCubeSideFirst t)))
      (remainingCubeSide_boundary _
        (FifthHurewicz.remainingCubeSide_boundary _
          (FourthHurewicz.remainingCubeSideFirst_boundary t ht)))
  have hL (t : I) (ht : t = 0 ∨ t = 1) :=
    evaluated_triangle_boundaryMap x a 4 productFourIntervalChain
      (remainingCubeSide (FifthHurewicz.remainingCubeSide
        (FourthHurewicz.remainingCubeSide (ThirdHurewicz.squareSideLeft t))))
      (remainingCubeSide_boundary _ (FifthHurewicz.remainingCubeSide_boundary _
        (FourthHurewicz.remainingCubeSide_boundary _
          (ThirdHurewicz.squareSideLeft_boundary t ht))))
  have hR (t : I) (ht : t = 0 ∨ t = 1) :=
    evaluated_triangle_boundaryMap x a 4 productFourIntervalChain
      (remainingCubeSide (FifthHurewicz.remainingCubeSide
        (FourthHurewicz.remainingCubeSide (ThirdHurewicz.squareSideRight t))))
      (remainingCubeSide_boundary _ (FifthHurewicz.remainingCubeSide_boundary _
        (FourthHurewicz.remainingCubeSide_boundary _
          (ThirdHurewicz.squareSideRight_boundary t ht))))
  simp only [remainingCubeChain_boundary, map_sub,
    hF 1 (Or.inr rfl), hF 0 (Or.inl rfl), hS 1 (Or.inr rfl), hS 0 (Or.inl rfl),
    hT 1 (Or.inr rfl), hT 0 (Or.inl rfl),
    hL 1 (Or.inr rfl), hL 0 (Or.inl rfl), hR 1 (Or.inr rfl), hR 0 (Or.inl rfl), sub_self]

end Wikipedia.HopfProblem.SixthHurewicz
