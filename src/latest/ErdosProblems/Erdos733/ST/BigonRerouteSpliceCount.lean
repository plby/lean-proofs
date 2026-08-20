import ErdosProblems.Erdos733.ST.BigonRerouteCrossingCountBound
import ErdosProblems.Erdos733.ST.BigonRerouteOrderedBetaTailData
import ErdosProblems.Erdos733.ST.OrdinaryPolygonalDrawing

open Classical
noncomputable section

-- [TABLET NODE: BigonRerouteSpliceCount]
lemma BigonRerouteSpliceCount {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet]
    (D : OrdinaryPolygonalDrawing G)
    (beta : G.edgeFinset) (u : V)
    (x y : EuclideanSpace ℝ (Fin 2))
    (B Bplus Rbeta H : Set (EuclideanSpace ℝ (Fin 2)))
    (XA XB Xnew newCrossingSet : Finset (EuclideanSpace ℝ (Fin 2)))
    (Bprefix betaArcNew : PolygonalArc)
    (edgeArcNew : G.edgeFinset → PolygonalArc)
    (Tail : BigonRerouteOrderedBetaTailData G D beta u y B Bplus Rbeta H) :
    u ∈ beta.1 →
      x ∈ D.crossingSet →
        x ∉ XB →
          XB ⊆ D.crossingSet →
            Xnew.card ≤ XA.card →
              newCrossingSet ⊆ (D.crossingSet.erase x \ XB) ∪ Xnew →
                Bprefix.source = D.vertexPlacement u →
                  Bprefix.target = y →
                    Bprefix.carrier ∩ Tail.tailArc.carrier =
                      ({y} : Set (EuclideanSpace ℝ (Fin 2))) →
                    edgeArcNew beta = betaArcNew →
                      (∀ edge : G.edgeFinset, edge ≠ beta →
                        edgeArcNew edge = D.edgeArc edge) →
                      betaArcNew.source = D.vertexPlacement u →
                        betaArcNew.target = D.vertexPlacement Tail.farEndpoint →
                          betaArcNew.carrier =
                              Bprefix.carrier ∪ Tail.tailArc.carrier →
                            Bprefix.carrier ⊆ betaArcNew.carrier →
                            (∀ e : G.edgeFinset,
                              ∃ a b : V,
                                G.Adj a b ∧ e.1 = Sym2.mk a b ∧
                                  (((edgeArcNew e).source =
                                      D.vertexPlacement a ∧
                                      (edgeArcNew e).target =
                                        D.vertexPlacement b) ∨
                                    ((edgeArcNew e).source =
                                      D.vertexPlacement b ∧
                                      (edgeArcNew e).target =
                                        D.vertexPlacement a))) →
                              (∀ (v : V) (e : G.edgeFinset),
                                D.vertexPlacement v ∉
                                  (edgeArcNew e).relativeInterior) →
                                (∀ ⦃e₁ e₂ e₃ : G.edgeFinset⦄
                                  ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
                                  e₁ ≠ e₂ → e₁ ≠ e₃ → e₂ ≠ e₃ →
                                    p ∈ (edgeArcNew e₁).relativeInterior →
                                      p ∈ (edgeArcNew e₂).relativeInterior →
                                        p ∈ (edgeArcNew e₃).relativeInterior →
                                          False) →
                                  (∀ ⦃e₁ e₂ : G.edgeFinset⦄
                                    ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
                                    e₁ ≠ e₂ →
                                      p ∈ (edgeArcNew e₁).relativeInterior →
                                        p ∈ (edgeArcNew e₂).relativeInterior →
                                          ∃ i j : ℕ,
                                            ∃ (hi :
                                                i + 1 <
                                                  (edgeArcNew e₁).vertices.length)
                                              (hj :
                                                j + 1 <
                                                  (edgeArcNew e₂).vertices.length),
                                              p ∈
                                                  segment ℝ
                                                    (edgeArcNew e₁).vertices[i]
                                                    (edgeArcNew e₁).vertices[i + 1] ∧
                                                p ∈
                                                  segment ℝ
                                                    (edgeArcNew e₂).vertices[j]
                                                    (edgeArcNew e₂).vertices[j + 1] ∧
                                                  ¬ ∃ c : ℝ,
                                                    (edgeArcNew e₂).vertices[j + 1] -
                                                        (edgeArcNew e₂).vertices[j] =
                                                      c •
                                                        ((edgeArcNew e₁).vertices[i + 1] -
                                                          (edgeArcNew e₁).vertices[i])) →
                                    (∀ ⦃e₁ e₂ : G.edgeFinset⦄,
                                      e₁ ≠ e₂ →
                                        ¬ ∃ i j : ℕ,
                                          ∃ (hi :
                                              i + 1 <
                                                (edgeArcNew e₁).vertices.length)
                                            (hj :
                                              j + 1 <
                                                (edgeArcNew e₂).vertices.length),
                                            ∃ p q : EuclideanSpace ℝ (Fin 2),
                                              p ≠ q ∧
                                                segment ℝ p q ⊆
                                                  segment ℝ
                                                      (edgeArcNew e₁).vertices[i]
                                                      (edgeArcNew e₁).vertices[i + 1] ∩
                                                    segment ℝ
                                                      (edgeArcNew e₂).vertices[j]
                                                      (edgeArcNew e₂).vertices[j + 1]) →
                                      (∀ p : EuclideanSpace ℝ (Fin 2),
                                        p ∈ newCrossingSet ↔
                                          ∃ e₁ e₂ : G.edgeFinset,
                                            e₁ ≠ e₂ ∧
                                              p ∈ (edgeArcNew e₁).relativeInterior ∧
                                                p ∈ (edgeArcNew e₂).relativeInterior) →
                                        ∃ D' : OrdinaryPolygonalDrawing G,
                                          D'.vertexPlacement = D.vertexPlacement ∧
                                            (∀ edge : G.edgeFinset,
                                              edge ≠ beta →
                                                D'.edgeArc edge =
                                                  D.edgeArc edge) ∧
                                              Bprefix.carrier ⊆
                                                (D'.edgeArc beta).carrier ∧
                                                D'.crossingSet.card +
                                                    XB.card + 1 ≤
                                                  D.crossingSet.card +
                                                    XA.card := by
-- BODY
  intro _huBeta hxold hxnotXB hXBsub hXnewCard hnewSubset _hPrefixSource
    _hPrefixTarget _hPrefixTailMeet hbetaEdge hotherEdges _hbetaSource
    _hbetaTarget _hbetaCarrier hBprefixSubset hEndpoints hNoVertex hNoThree
    hTransverse hNoShared hCrossSpec
  let D' : OrdinaryPolygonalDrawing G :=
    { vertexPlacement := D.vertexPlacement
      vertexPlacement_injective := D.vertexPlacement_injective
      edgeArc := edgeArcNew
      edgeArc_endpoints := hEndpoints
      crossingSet := newCrossingSet
      no_vertex_in_edge_interior := hNoVertex
      no_three_edge_interiors_meet := by
        intro e₁ e₂ e₃ p he₁₂ he₁₃ he₂₃ hp₁ hp₂ hp₃
        exact hNoThree he₁₂ he₁₃ he₂₃ hp₁ hp₂ hp₃
      transverse_intersections := by
        intro e₁ e₂ p he₁₂ hp₁ hp₂
        exact hTransverse he₁₂ hp₁ hp₂
      no_shared_nondegenerate_subarc := by
        intro e₁ e₂ he₁₂
        exact hNoShared he₁₂
      crossingSet_spec := hCrossSpec
      adjacentEdgeCrossingCount :=
        (newCrossingSet.filter (fun p =>
          ∃ e₁ e₂ : G.edgeFinset,
            e₁ ≠ e₂ ∧
              (∃ v : V, v ∈ e₁.1 ∧ v ∈ e₂.1) ∧
                p ∈ (edgeArcNew e₁).relativeInterior ∧
                  p ∈ (edgeArcNew e₂).relativeInterior)).card
      adjacentEdgeCrossingCount_eq := rfl }
  refine ⟨D', rfl, ?_, ?_, ?_⟩
  · intro edge hedge
    change edgeArcNew edge = D.edgeArc edge
    exact hotherEdges edge hedge
  · change Bprefix.carrier ⊆ (edgeArcNew beta).carrier
    simpa [hbetaEdge] using hBprefixSubset
  · change newCrossingSet.card + XB.card + 1 ≤ D.crossingSet.card + XA.card
    exact
      BigonRerouteCrossingCountBound D.crossingSet newCrossingSet XB Xnew XA x
        hxold hxnotXB hXBsub hXnewCard hnewSubset
