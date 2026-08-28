import Wikipedia.HomotopyGroupsOfSpheres.SeventhHurewicz.ChainsBoundaryGeometry

/-! # Based evaluation cancels the six-cube boundary in the actual chain groups -/

noncomputable section

open scoped unitInterval Topology

namespace Wikipedia.HomotopyGroupsOfSpheres.SeventhHurewicz

open Wikipedia.HopfProblem
open FirstHurewicz SingularMayerVietoris PeriodTorusHigherHomology

attribute [local instance] integerLinearMapModule integerTensorModule

variable {X A : Type} [TopologicalSpace X] [TopologicalSpace A]

/-- A boundary-valued parameter map has its constant evaluated edge-product image,
for parameter chains of every degree. -/
theorem evaluated_edge_boundaryMap (x : X) (a : Chains (BasedLoopSpace x) 1)
    (k : ℕ) (b : Chains A k) (f : C(A, Fin 6 → I))
    (hf : ∀ t, f t ∈ Cube.boundary (Fin 6)) :
    inducedChain (evaluation x) (k + 1)
        (crossProductEdge (BasedLoopSpace x) (Fin 6 → I) k a (inducedChain f k b)) =
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
    (k : ℕ) (b : Chains A k) (f : C(A, Fin 6 → I))
    (hf : ∀ t, f t ∈ Cube.boundary (Fin 6)) :
    inducedChain (evaluation x) (k + 2)
        (crossProductTriangle (BasedLoopSpace x) (Fin 6 → I) k a (inducedChain f k b)) =
      inducedChain (ContinuousMap.const (BasedLoopSpace x × A) x) (k + 2)
        (crossProductTriangle (BasedLoopSpace x) A k a b) := by
  have h := crossProductTriangle_natural (ContinuousMap.id (BasedLoopSpace x)) f k a b
  rw [inducedChain_id, LinearMap.id_apply] at h
  rw [← h]
  change ((inducedChain (evaluation x) (k + 2)).comp
    (inducedChain ((ContinuousMap.id (BasedLoopSpace x)).prodMap f) (k + 2))) _ = _
  rw [← inducedChain_comp, evaluation_comp_boundary x f hf]

/-- All six opposite pairs cancel after evaluated edge crossing. -/
theorem evaluated_edge_cubeBoundary_cancel (x : X)
    (a : Chains (BasedLoopSpace x) 1) :
    inducedChain (evaluation x) 6
        (crossProductEdge (BasedLoopSpace x) (Fin 6 → I) 5 a
          (((singularComplex (Fin 6 → I)).d 6 5).hom
            SixthHurewicz.fundamentalCubeChain)) = 0 := by
  have h0 (t : I) (ht : t = 0 ∨ t = 1) :=
    evaluated_edge_boundaryMap x a 5 FifthHurewicz.fundamentalCubeChain
      (boundaryFace0 t) (boundaryFace0_boundary t ht)
  have h1 (t : I) (ht : t = 0 ∨ t = 1) :=
    evaluated_edge_boundaryMap x a 5 FifthHurewicz.productCubeChain
      (boundaryFace1 t) (boundaryFace1_boundary t ht)
  have h2 (t : I) (ht : t = 0 ∨ t = 1) :=
    evaluated_edge_boundaryMap x a 5 productTwoIntervalCubeChain
      (boundaryFace2 t) (boundaryFace2_boundary t ht)
  have h3 (t : I) (ht : t = 0 ∨ t = 1) :=
    evaluated_edge_boundaryMap x a 5 productThreeIntervalSquareChain
      (boundaryFace3 t) (boundaryFace3_boundary t ht)
  have h4 (t : I) (ht : t = 0 ∨ t = 1) :=
    evaluated_edge_boundaryMap x a 5 productFiveIntervalChain
      (boundaryFace4 t) (boundaryFace4_boundary t ht)
  have h5 (t : I) (ht : t = 0 ∨ t = 1) :=
    evaluated_edge_boundaryMap x a 5 productFiveIntervalChain
      (boundaryFace5 t) (boundaryFace5_boundary t ht)
  simp only [remainingCubeChain_boundary, map_sub,
    h0 1 (Or.inr rfl), h0 0 (Or.inl rfl),
    h1 1 (Or.inr rfl), h1 0 (Or.inl rfl),
    h2 1 (Or.inr rfl), h2 0 (Or.inl rfl),
    h3 1 (Or.inr rfl), h3 0 (Or.inl rfl),
    h4 1 (Or.inr rfl), h4 0 (Or.inl rfl),
    h5 1 (Or.inr rfl), h5 0 (Or.inl rfl),
    sub_self]

/-- All six opposite pairs cancel after evaluated triangle crossing. -/
theorem evaluated_triangle_cubeBoundary_cancel (x : X)
    (a : Chains (BasedLoopSpace x) 2) :
    inducedChain (evaluation x) 7
        (crossProductTriangle (BasedLoopSpace x) (Fin 6 → I) 5 a
          (((singularComplex (Fin 6 → I)).d 6 5).hom
            SixthHurewicz.fundamentalCubeChain)) = 0 := by
  have h0 (t : I) (ht : t = 0 ∨ t = 1) :=
    evaluated_triangle_boundaryMap x a 5 FifthHurewicz.fundamentalCubeChain
      (boundaryFace0 t) (boundaryFace0_boundary t ht)
  have h1 (t : I) (ht : t = 0 ∨ t = 1) :=
    evaluated_triangle_boundaryMap x a 5 FifthHurewicz.productCubeChain
      (boundaryFace1 t) (boundaryFace1_boundary t ht)
  have h2 (t : I) (ht : t = 0 ∨ t = 1) :=
    evaluated_triangle_boundaryMap x a 5 productTwoIntervalCubeChain
      (boundaryFace2 t) (boundaryFace2_boundary t ht)
  have h3 (t : I) (ht : t = 0 ∨ t = 1) :=
    evaluated_triangle_boundaryMap x a 5 productThreeIntervalSquareChain
      (boundaryFace3 t) (boundaryFace3_boundary t ht)
  have h4 (t : I) (ht : t = 0 ∨ t = 1) :=
    evaluated_triangle_boundaryMap x a 5 productFiveIntervalChain
      (boundaryFace4 t) (boundaryFace4_boundary t ht)
  have h5 (t : I) (ht : t = 0 ∨ t = 1) :=
    evaluated_triangle_boundaryMap x a 5 productFiveIntervalChain
      (boundaryFace5 t) (boundaryFace5_boundary t ht)
  simp only [remainingCubeChain_boundary, map_sub,
    h0 1 (Or.inr rfl), h0 0 (Or.inl rfl),
    h1 1 (Or.inr rfl), h1 0 (Or.inl rfl),
    h2 1 (Or.inr rfl), h2 0 (Or.inl rfl),
    h3 1 (Or.inr rfl), h3 0 (Or.inl rfl),
    h4 1 (Or.inr rfl), h4 0 (Or.inl rfl),
    h5 1 (Or.inr rfl), h5 0 (Or.inl rfl),
    sub_self]

end Wikipedia.HomotopyGroupsOfSpheres.SeventhHurewicz
