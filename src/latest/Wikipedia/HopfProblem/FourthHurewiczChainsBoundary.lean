import Wikipedia.HopfProblem.FourthHurewiczChainsBoundaryGeometry

/-!
# Cancellation of the remaining cube boundary under based evaluation

Every map into the boundary of the remaining three-cube evaluates
constantly. Naturality of the genuine chain cross products therefore
identifies the two faces in each opposite pair. Their signs cancel as
singular chains, before passing to homology.
-/

noncomputable section

open scoped unitInterval Topology

namespace Wikipedia.HopfProblem.FourthHurewicz

open FirstHurewicz SingularMayerVietoris PeriodTorusHigherHomology

attribute [local instance] integerLinearMapModule integerTensorModule

variable {X A : Type} [TopologicalSpace X] [TopologicalSpace A]

/-- Every boundary-square factor has its constant evaluated three-chain image. -/
theorem evaluated_edge_boundaryMap (x : X) (a : Chains (BasedLoopSpace x) 1)
    (b : Chains A 2) (f : C(A, Fin 3 → I))
    (hf : ∀ t, f t ∈ Cube.boundary (Fin 3)) :
    inducedChain (evaluation x) 3
        (crossProductEdge (BasedLoopSpace x) (Fin 3 → I) 2 a (inducedChain f 2 b)) =
      inducedChain (ContinuousMap.const (BasedLoopSpace x × A) x) 3
        (crossProductEdge (BasedLoopSpace x) A 2 a b) := by
  have h := crossProductEdge_natural (ContinuousMap.id (BasedLoopSpace x)) f 2 a b
  rw [inducedChain_id, LinearMap.id_apply] at h
  rw [← h]
  change ((inducedChain (evaluation x) 3).comp
    (inducedChain ((ContinuousMap.id (BasedLoopSpace x)).prodMap f) 3)) _ = _
  rw [← inducedChain_comp, evaluation_comp_boundary x f hf]

/-- The corresponding evaluated four-chain image for a degree-two left factor. -/
theorem evaluated_triangle_boundaryMap (x : X) (a : Chains (BasedLoopSpace x) 2)
    (b : Chains A 2) (f : C(A, Fin 3 → I))
    (hf : ∀ t, f t ∈ Cube.boundary (Fin 3)) :
    inducedChain (evaluation x) 4
        (crossProductTriangle (BasedLoopSpace x) (Fin 3 → I) 2 a (inducedChain f 2 b)) =
      inducedChain (ContinuousMap.const (BasedLoopSpace x × A) x) 4
        (crossProductTriangle (BasedLoopSpace x) A 2 a b) := by
  have h := crossProductTriangle_natural (ContinuousMap.id (BasedLoopSpace x)) f 2 a b
  rw [inducedChain_id, LinearMap.id_apply] at h
  rw [← h]
  change ((inducedChain (evaluation x) 4).comp
    (inducedChain ((ContinuousMap.id (BasedLoopSpace x)).prodMap f) 4)) _ = _
  rw [← inducedChain_comp, evaluation_comp_boundary x f hf]

/-- The complete remaining-cube boundary vanishes after evaluated edge crossing. -/
theorem evaluated_edge_cubeBoundary_cancel (x : X) (a : Chains (BasedLoopSpace x) 1) :
    inducedChain (evaluation x) 3
        (crossProductEdge (BasedLoopSpace x) (Fin 3 → I) 2 a
          (((singularComplex (Fin 3 → I)).d 3 2).hom
            ThirdHurewicz.fundamentalCubeChain)) = 0 := by
  have hF (t : I) (ht : t = 0 ∨ t = 1) :=
    evaluated_edge_boundaryMap x a SecondHurewicz.fundamentalSquareChain
      (remainingCubeSideFirst t) (remainingCubeSideFirst_boundary t ht)
  have hL (t : I) (ht : t = 0 ∨ t = 1) :=
    evaluated_edge_boundaryMap x a SecondHurewicz.productSquareChain
      (remainingCubeSide (ThirdHurewicz.squareSideLeft t))
      (remainingCubeSide_boundary _ (ThirdHurewicz.squareSideLeft_boundary t ht))
  have hR (t : I) (ht : t = 0 ∨ t = 1) :=
    evaluated_edge_boundaryMap x a SecondHurewicz.productSquareChain
      (remainingCubeSide (ThirdHurewicz.squareSideRight t))
      (remainingCubeSide_boundary _ (ThirdHurewicz.squareSideRight_boundary t ht))
  simp only [remainingCubeChain_boundary, map_sub,
    hF 1 (Or.inr rfl), hF 0 (Or.inl rfl), hL 1 (Or.inr rfl), hL 0 (Or.inl rfl),
    hR 1 (Or.inr rfl), hR 0 (Or.inl rfl), sub_self]

/-- The same exact cancellation with a degree-two left factor. -/
theorem evaluated_triangle_cubeBoundary_cancel (x : X) (a : Chains (BasedLoopSpace x) 2) :
    inducedChain (evaluation x) 4
        (crossProductTriangle (BasedLoopSpace x) (Fin 3 → I) 2 a
          (((singularComplex (Fin 3 → I)).d 3 2).hom
            ThirdHurewicz.fundamentalCubeChain)) = 0 := by
  have hF (t : I) (ht : t = 0 ∨ t = 1) :=
    evaluated_triangle_boundaryMap x a SecondHurewicz.fundamentalSquareChain
      (remainingCubeSideFirst t) (remainingCubeSideFirst_boundary t ht)
  have hL (t : I) (ht : t = 0 ∨ t = 1) :=
    evaluated_triangle_boundaryMap x a SecondHurewicz.productSquareChain
      (remainingCubeSide (ThirdHurewicz.squareSideLeft t))
      (remainingCubeSide_boundary _ (ThirdHurewicz.squareSideLeft_boundary t ht))
  have hR (t : I) (ht : t = 0 ∨ t = 1) :=
    evaluated_triangle_boundaryMap x a SecondHurewicz.productSquareChain
      (remainingCubeSide (ThirdHurewicz.squareSideRight t))
      (remainingCubeSide_boundary _ (ThirdHurewicz.squareSideRight_boundary t ht))
  simp only [remainingCubeChain_boundary, map_sub,
    hF 1 (Or.inr rfl), hF 0 (Or.inl rfl), hL 1 (Or.inr rfl), hL 0 (Or.inl rfl),
    hR 1 (Or.inr rfl), hR 0 (Or.inl rfl), sub_self]

end Wikipedia.HopfProblem.FourthHurewicz
