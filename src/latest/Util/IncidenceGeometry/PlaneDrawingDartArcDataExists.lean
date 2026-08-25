import Util.IncidenceGeometry.PlaneDrawingDartArcData
import Util.IncidenceGeometry.OrdinaryPolygonalDrawing
import Util.IncidenceGeometry.PolygonalArc
import Util.IncidenceGeometry.PolygonalArcReverse

open Classical
noncomputable section

lemma PlaneDrawingDartArcDataExists {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet] [DecidableRel G.Adj]
    (D : OrdinaryPolygonalDrawing G) (hD : D.crossingSet.card = 0) :
    Nonempty (PlaneDrawingDartArcData G D) := by
  have _hD := hD
  let edgeOfDart : G.Dart → G.edgeFinset := fun d =>
    ⟨d.edge, by
      rw [SimpleGraph.mem_edgeFinset]
      exact SimpleGraph.Dart.edge_mem d⟩
  have edgeOfDart_eq : ∀ d : G.Dart, (edgeOfDart d).1 = d.edge := by
    intro d
    rfl
  have endpoint_or : ∀ d : G.Dart,
      (((D.edgeArc (edgeOfDart d)).source = D.vertexPlacement d.toProd.1 ∧
          (D.edgeArc (edgeOfDart d)).target = D.vertexPlacement d.toProd.2) ∨
        ((D.edgeArc (edgeOfDart d)).source = D.vertexPlacement d.toProd.2 ∧
          (D.edgeArc (edgeOfDart d)).target = D.vertexPlacement d.toProd.1)) := by
    intro d
    rcases D.edgeArc_endpoints (edgeOfDart d) with ⟨u, v, _huv_adj, huv_edge, horient⟩
    have hsym : Sym2.mk d.toProd.1 d.toProd.2 = Sym2.mk u v := by
      have hde : d.edge = Sym2.mk u v := by
        exact (edgeOfDart_eq d).symm.trans huv_edge
      simpa [SimpleGraph.Dart.edge] using hde
    rcases (Sym2.eq_iff.mp hsym) with hsame | hswap
    · rcases hsame with ⟨htail, hhead⟩
      subst u
      subst v
      simpa using horient
    · rcases hswap with ⟨htail, hhead⟩
      subst u
      subst v
      rcases horient with hforward | hback
      · exact Or.inr hforward
      · exact Or.inl hback
  let dartArc : G.Dart → PolygonalArc := fun d =>
    if (D.edgeArc (edgeOfDart d)).source = D.vertexPlacement d.toProd.1 then
      D.edgeArc (edgeOfDart d)
    else
      PolygonalArcReverse (D.edgeArc (edgeOfDart d))
  refine ⟨{
    dartEdge := edgeOfDart
    dartEdge_eq := edgeOfDart_eq
    dartArc := dartArc
    dartArc_orientation := ?_
    dartArc_carrier := ?_
    dartArc_source := ?_
    dartArc_target := ?_
    dartArc_symm_eq_reverse := ?_ }⟩
  · intro d
    dsimp [dartArc]
    by_cases h : (D.edgeArc (edgeOfDart d)).source = D.vertexPlacement d.toProd.1
    · exact Or.inl ⟨by simp [h], h⟩
    · have hcases := endpoint_or d
      rcases hcases with hforward | hback
      · exact False.elim (h hforward.1)
      · exact Or.inr ⟨by simp [h], hback.2⟩
  · intro d
    dsimp [dartArc]
    split_ifs with h
    · rfl
    · simp [PolygonalArcReverse]
  · intro d
    dsimp [dartArc]
    by_cases h : (D.edgeArc (edgeOfDart d)).source = D.vertexPlacement d.toProd.1
    · simp [h]
    · have hcases := endpoint_or d
      rcases hcases with hforward | hback
      · exact False.elim (h hforward.1)
      · simp [h, PolygonalArcReverse, hback.2]
  · intro d
    dsimp [dartArc]
    by_cases h : (D.edgeArc (edgeOfDart d)).source = D.vertexPlacement d.toProd.1
    · have hcases := endpoint_or d
      rcases hcases with hforward | hback
      · simp [h, hforward.2]
      · have htail_head : d.toProd.2 = d.toProd.1 := by
          apply D.vertexPlacement_injective
          calc
            D.vertexPlacement d.toProd.2 = (D.edgeArc (edgeOfDart d)).source := by
              simpa using hback.1.symm
            _ = D.vertexPlacement d.toProd.1 := h
        have hadj : G.Adj d.toProd.1 d.toProd.1 := by
          simpa [htail_head] using d.adj
        exact False.elim ((G.loopless.irrefl d.toProd.1) hadj)
    · have hcases := endpoint_or d
      rcases hcases with hforward | hback
      · exact False.elim (h hforward.1)
      · have hneq : ¬ D.vertexPlacement d.toProd.2 = D.vertexPlacement d.toProd.1 := by
          intro hv
          exact h (hback.1.trans hv)
        simp [hneq, PolygonalArcReverse, hback.1]
  · intro d
    have hedge_symm : edgeOfDart d.symm = edgeOfDart d := by
      apply Subtype.ext
      simp [edgeOfDart, SimpleGraph.Dart.edge_symm]
    have hvertex_ne :
        D.vertexPlacement d.toProd.1 ≠ D.vertexPlacement d.toProd.2 := by
      intro hv
      have htail_head : d.toProd.1 = d.toProd.2 :=
        D.vertexPlacement_injective hv
      have hadj : G.Adj d.toProd.1 d.toProd.1 := by
        simpa [htail_head] using d.adj
      exact (G.loopless.irrefl d.toProd.1) hadj
    have hvertex_ne' :
        ¬ D.vertexPlacement d.toProd.2 = D.vertexPlacement d.toProd.1 := by
      exact fun hv => hvertex_ne hv.symm
    dsimp [dartArc]
    by_cases h : (D.edgeArc (edgeOfDart d)).source = D.vertexPlacement d.toProd.1
    · simp [h, hvertex_ne, hedge_symm]
    · have hsource_head : (D.edgeArc (edgeOfDart d)).source =
          D.vertexPlacement d.toProd.2 := by
        have hcases := endpoint_or d
        rcases hcases with hforward | hback
        · exact False.elim (h hforward.1)
        · simpa using hback.1
      have hdouble :
          PolygonalArcReverse (PolygonalArcReverse (D.edgeArc (edgeOfDart d))) =
            D.edgeArc (edgeOfDart d) := by
        cases D.edgeArc (edgeOfDart d)
        simp [PolygonalArcReverse]
      simp [hsource_head, hvertex_ne', hedge_symm, hdouble]
