import ErdosProblems.Erdos733.ST.OrdinaryPolygonalDrawing

open Classical
noncomputable section

-- [TABLET NODE: OrdinaryDrawingPartialData]
structure OrdinaryDrawingPartialData {V : Type*} [Fintype V] (G : SimpleGraph V)
    [Fintype G.edgeSet] (drawn : Finset G.edgeFinset) where
-- BODY
  vertexPlacement : V → EuclideanSpace ℝ (Fin 2)
  vertexPlacement_injective : Function.Injective vertexPlacement
  edgeArc : {e : G.edgeFinset // e ∈ drawn} → PolygonalArc
  edgeArc_endpoints :
    ∀ e : {e : G.edgeFinset // e ∈ drawn},
      ∃ u v : V,
        G.Adj u v ∧ (e.1 : G.edgeFinset).1 = Sym2.mk u v ∧
          (((edgeArc e).source = vertexPlacement u ∧
              (edgeArc e).target = vertexPlacement v) ∨
            ((edgeArc e).source = vertexPlacement v ∧
              (edgeArc e).target = vertexPlacement u))
  crossingSet : Finset (EuclideanSpace ℝ (Fin 2))
  no_vertex_in_edge_interior :
    ∀ (v : V) (e : {e : G.edgeFinset // e ∈ drawn}),
      vertexPlacement v ∉ (edgeArc e).relativeInterior
  no_three_edge_interiors_meet :
    ∀ ⦃e₁ e₂ e₃ : {e : G.edgeFinset // e ∈ drawn}⦄
      ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
      e₁ ≠ e₂ → e₁ ≠ e₃ → e₂ ≠ e₃ →
        p ∈ (edgeArc e₁).relativeInterior →
          p ∈ (edgeArc e₂).relativeInterior →
            p ∈ (edgeArc e₃).relativeInterior → False
  transverse_intersections :
    ∀ ⦃e₁ e₂ : {e : G.edgeFinset // e ∈ drawn}⦄
      ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
      e₁ ≠ e₂ →
        p ∈ (edgeArc e₁).relativeInterior →
          p ∈ (edgeArc e₂).relativeInterior →
            ∃ i j : ℕ,
              ∃ (hi : i + 1 < (edgeArc e₁).vertices.length)
                (hj : j + 1 < (edgeArc e₂).vertices.length),
                p ∈ segment ℝ (edgeArc e₁).vertices[i] (edgeArc e₁).vertices[i + 1] ∧
                  p ∈ segment ℝ (edgeArc e₂).vertices[j] (edgeArc e₂).vertices[j + 1] ∧
                    ¬ ∃ c : ℝ,
                      (edgeArc e₂).vertices[j + 1] - (edgeArc e₂).vertices[j] =
                        c • ((edgeArc e₁).vertices[i + 1] - (edgeArc e₁).vertices[i])
  no_shared_nondegenerate_subarc :
    ∀ ⦃e₁ e₂ : {e : G.edgeFinset // e ∈ drawn}⦄,
      e₁ ≠ e₂ →
        ¬ ∃ i j : ℕ,
          ∃ (hi : i + 1 < (edgeArc e₁).vertices.length)
            (hj : j + 1 < (edgeArc e₂).vertices.length),
            ∃ p q : EuclideanSpace ℝ (Fin 2),
              p ≠ q ∧
                segment ℝ p q ⊆
                  segment ℝ (edgeArc e₁).vertices[i] (edgeArc e₁).vertices[i + 1] ∩
                    segment ℝ (edgeArc e₂).vertices[j] (edgeArc e₂).vertices[j + 1]
  crossingSet_spec :
    ∀ p : EuclideanSpace ℝ (Fin 2),
      p ∈ crossingSet ↔
        ∃ e₁ e₂ : {e : G.edgeFinset // e ∈ drawn},
          e₁ ≠ e₂ ∧
            p ∈ (edgeArc e₁).relativeInterior ∧
              p ∈ (edgeArc e₂).relativeInterior
