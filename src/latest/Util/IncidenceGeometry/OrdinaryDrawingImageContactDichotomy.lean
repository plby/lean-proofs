import Util.IncidenceGeometry.PlaneFaceData
import Util.IncidenceGeometry.OrdinaryDrawingImage

open Classical
noncomputable section

lemma OrdinaryDrawingImageContactDichotomy {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet] [DecidableRel G.Adj]
    (D : OrdinaryPolygonalDrawing G) (A : PlaneFaceData G D) :
    ∀ x : EuclideanSpace ℝ (Fin 2),
      x ∈ OrdinaryDrawingImage G D →
        (∃ v : V, x = D.vertexPlacement v) ∨
          ∃ d : G.Dart, x ∈ (A.dartArc d).relativeInterior := by
  intro x hx
  rw [OrdinaryDrawingImage] at hx
  rcases hx with hxVertex | hxEdge
  · left
    rcases hxVertex with ⟨v, hv⟩
    exact ⟨v, hv.symm⟩
  · rcases Set.mem_iUnion.1 hxEdge with ⟨e, hxCarrier⟩
    rcases D.edgeArc_endpoints e with ⟨u, v, huv, huv_edge, hends⟩
    by_cases hxRel : x ∈ (D.edgeArc e).relativeInterior
    · right
      let d : G.Dart := ⟨(u, v), huv⟩
      have hd : d.edge = e.1 := by
        simpa [d, SimpleGraph.Dart.edge] using huv_edge.symm
      have hdartEdge : A.dartEdge d = e := by
        apply Subtype.ext
        exact (A.dartEdge_eq d).trans hd
      have hcarrier : (A.dartArc d).carrier = (D.edgeArc e).carrier := by
        simpa [hdartEdge] using A.dartArc_carrier d
      have hDendpoints :
          ({(D.edgeArc e).source, (D.edgeArc e).target} :
              Set (EuclideanSpace ℝ (Fin 2))) =
            {D.vertexPlacement d.toProd.1, D.vertexPlacement d.toProd.2} := by
        rcases hends with hdir | hdir
        · rcases hdir with ⟨hsource, htarget⟩
          simp [d, hsource, htarget]
        · rcases hdir with ⟨hsource, htarget⟩
          simp [d, hsource, htarget, Set.pair_comm]
      have hdartEndpoints :
          ({(A.dartArc d).source, (A.dartArc d).target} :
              Set (EuclideanSpace ℝ (Fin 2))) =
            {D.vertexPlacement d.toProd.1, D.vertexPlacement d.toProd.2} := by
        simp [A.dartArc_source d, A.dartArc_target d]
      have hdartRelEq :
          (A.dartArc d).relativeInterior = (D.edgeArc e).relativeInterior := by
        rw [(A.dartArc d).relativeInterior_eq, (D.edgeArc e).relativeInterior_eq,
          hcarrier, hdartEndpoints, ← hDendpoints]
      exact ⟨d, by simpa [hdartRelEq] using hxRel⟩
    · left
      have hxEndpoint :
          x ∈ ({(D.edgeArc e).source, (D.edgeArc e).target} :
              Set (EuclideanSpace ℝ (Fin 2))) := by
        rw [(D.edgeArc e).relativeInterior_eq] at hxRel
        by_contra hxNotEndpoint
        exact hxRel ⟨hxCarrier, hxNotEndpoint⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hxEndpoint
      rcases hends with hdir | hdir
      · rcases hdir with ⟨hsource, htarget⟩
        rcases hxEndpoint with hxSource | hxTarget
        · exact ⟨u, hxSource.trans hsource⟩
        · exact ⟨v, hxTarget.trans htarget⟩
      · rcases hdir with ⟨hsource, htarget⟩
        rcases hxEndpoint with hxSource | hxTarget
        · exact ⟨v, hxSource.trans hsource⟩
        · exact ⟨u, hxTarget.trans htarget⟩

