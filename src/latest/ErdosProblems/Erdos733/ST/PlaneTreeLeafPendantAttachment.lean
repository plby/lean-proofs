import ErdosProblems.Erdos733.ST.CrossingFreeEdgeInteriorDisjoint
import ErdosProblems.Erdos733.ST.OrdinaryDrawingImage
import ErdosProblems.Erdos733.ST.OrdinaryPolygonalDrawing
import ErdosProblems.Erdos733.ST.PolygonalArcVertexMemCarrier

open Classical
noncomputable section

-- [TABLET NODE: PlaneTreeLeafPendantAttachment]
lemma PlaneTreeLeafPendantAttachment {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet] [DecidableRel G.Adj]
    (D : OrdinaryPolygonalDrawing G) (hD : D.crossingSet.card = 0)
    {v w : V} (e : G.edgeFinset) :
    let S : Set V := ({v}ᶜ : Set V)
    ∀ (D' : OrdinaryPolygonalDrawing (G.induce S)),
      (∀ x : S, D'.vertexPlacement x = D.vertexPlacement x.1) →
        (∀ ed : (G.induce S).edgeFinset,
          ∃ eG : G.edgeFinset,
            eG.1 = Sym2.map (Subtype.val : S → V) ed.1 ∧
              eG.1 ≠ e.1 ∧
                D'.edgeArc ed = D.edgeArc eG) →
          D.vertexPlacement w ∈ OrdinaryDrawingImage (G.induce S) D' →
            D.vertexPlacement v ∉ OrdinaryDrawingImage (G.induce S) D' →
              (((D.edgeArc e).source = D.vertexPlacement v ∧
                  (D.edgeArc e).target = D.vertexPlacement w) ∨
                ((D.edgeArc e).source = D.vertexPlacement w ∧
                  (D.edgeArc e).target = D.vertexPlacement v)) →
                (((D.edgeArc e).carrier ∩ OrdinaryDrawingImage (G.induce S) D' =
                    ({(D.edgeArc e).source} : Set (EuclideanSpace ℝ (Fin 2))) ∧
                    (D.edgeArc e).target ∉ OrdinaryDrawingImage (G.induce S) D') ∨
                  ((D.edgeArc e).carrier ∩ OrdinaryDrawingImage (G.induce S) D' =
                    ({(D.edgeArc e).target} : Set (EuclideanSpace ℝ (Fin 2))) ∧
                    (D.edgeArc e).source ∉ OrdinaryDrawingImage (G.induce S) D')) := by
-- BODY
  intro S D' hD'_vertex hD'_edges hAttach_mem hLeafEndpoint_notMem
    hEndpointOrientation
  let γ : PolygonalArc := D.edgeArc e
  let K : Set (EuclideanSpace ℝ (Fin 2)) := OrdinaryDrawingImage (G.induce S) D'
  have endpoint_of_not_rel :
      ∀ (δ : PolygonalArc) ⦃y : EuclideanSpace ℝ (Fin 2)⦄,
        y ∈ δ.carrier → y ∉ δ.relativeInterior →
          y = δ.source ∨ y = δ.target := by
    intro δ y hy hnot
    have hyEnd : y ∈ ({δ.source, δ.target} : Set (EuclideanSpace ℝ (Fin 2))) := by
      by_contra hnotEnd
      have hyRel : y ∈ δ.relativeInterior := by
        rw [δ.relativeInterior_eq]
        exact ⟨hy, hnotEnd⟩
      exact hnot hyRel
    simpa using hyEnd
  have hγsource_mem : γ.source ∈ γ.carrier := by
    have h0 : 0 < γ.vertices.length := by
      have hlen := γ.length_ge_two
      omega
    have hsource : γ.vertices[0]'h0 = γ.source := by
      have hhead := γ.source_eq_head
      rw [List.head?_eq_getElem?] at hhead
      rw [List.getElem?_eq_getElem h0] at hhead
      exact Option.some.inj hhead
    exact PolygonalArcVertexMemCarrier γ (by
      rw [← hsource]
      exact List.getElem_mem (l := γ.vertices) (n := 0) h0)
  have hγtarget_mem : γ.target ∈ γ.carrier := by
    have hlast_lt : γ.vertices.length - 1 < γ.vertices.length := by
      have hlen := γ.length_ge_two
      omega
    have htarget : γ.vertices[γ.vertices.length - 1]'hlast_lt = γ.target := by
      have hlast := γ.target_eq_last
      rw [List.getLast?_eq_getElem?] at hlast
      rw [List.getElem?_eq_getElem hlast_lt] at hlast
      exact Option.some.inj hlast
    exact PolygonalArcVertexMemCarrier γ (by
      rw [← htarget]
      exact
        List.getElem_mem (l := γ.vertices) (n := γ.vertices.length - 1) hlast_lt)
  have endpoint_on_K_is_attachment :
      ∀ ⦃x : EuclideanSpace ℝ (Fin 2)⦄,
        x ∈ γ.carrier → x ∈ K → x ∉ γ.relativeInterior →
          x = D.vertexPlacement w := by
    intro x hxγ hxK hxγnot
    rcases endpoint_of_not_rel γ hxγ hxγnot with hxsrc | hxtgt
    · rcases hEndpointOrientation with hdir | hrev
      · exact False.elim (hLeafEndpoint_notMem (by
          simpa [K, γ, hxsrc, hdir.1] using hxK))
      · simpa [γ, hxsrc, hrev.1]
    · rcases hEndpointOrientation with hdir | hrev
      · simpa [γ, hxtgt, hdir.2]
      · exact False.elim (hLeafEndpoint_notMem (by
          simpa [K, γ, hxtgt, hrev.2] using hxK))
  have common_point_is_attachment :
      ∀ ⦃x : EuclideanSpace ℝ (Fin 2)⦄,
        x ∈ γ.carrier → x ∈ K → x = D.vertexPlacement w := by
    intro x hxγ hxK
    have hxK_cases : x ∈ OrdinaryDrawingImage (G.induce S) D' := by
      simpa [K] using hxK
    rw [OrdinaryDrawingImage] at hxK_cases
    rcases hxK_cases with hxVertex | hxEdge
    · rcases hxVertex with ⟨u, hxu⟩
      have hxγnot : x ∉ γ.relativeInterior := by
        intro hxγrel
        have huRel : D.vertexPlacement u.1 ∈ (D.edgeArc e).relativeInterior := by
          have hxγrel' := hxγrel
          rw [← hxu, hD'_vertex u] at hxγrel'
          simpa [γ] using hxγrel'
        exact D.no_vertex_in_edge_interior u.1 e huRel
      exact endpoint_on_K_is_attachment hxγ hxK hxγnot
    · rcases Set.mem_iUnion.mp hxEdge with ⟨ed, hxed⟩
      rcases hD'_edges ed with ⟨eG, _heGmap, heG_ne, hArc⟩
      have hxOldCarrier : x ∈ (D.edgeArc eG).carrier := by
        simpa [hArc] using hxed
      by_cases hxγrel : x ∈ γ.relativeInterior
      · by_cases hxOldRel : x ∈ (D.edgeArc eG).relativeInterior
        · have he_ne_eG : e ≠ eG := by
            intro heq
            exact heG_ne (by simpa [heq])
          exact False.elim
            (CrossingFreeEdgeInteriorDisjoint G D hD he_ne_eG
              (by simpa [γ] using hxγrel) hxOldRel)
        · have hxOldEnd := endpoint_of_not_rel (D.edgeArc eG) hxOldCarrier hxOldRel
          have hxVertexOld : ∃ u : V, x = D.vertexPlacement u := by
            rcases D.edgeArc_endpoints eG with ⟨a, b, _hab, _hedge, hends⟩
            rcases hxOldEnd with hxsrc | hxtgt
            · rcases hends with hdir | hrev
              · exact ⟨a, by rw [hxsrc, hdir.1]⟩
              · exact ⟨b, by rw [hxsrc, hrev.1]⟩
            · rcases hends with hdir | hrev
              · exact ⟨b, by rw [hxtgt, hdir.2]⟩
              · exact ⟨a, by rw [hxtgt, hrev.2]⟩
          rcases hxVertexOld with ⟨u, hxVertexEq⟩
          have huRel : D.vertexPlacement u ∈ (D.edgeArc e).relativeInterior := by
            simpa [γ, hxVertexEq] using hxγrel
          exact False.elim (D.no_vertex_in_edge_interior u e huRel)
      · exact endpoint_on_K_is_attachment hxγ hxK hxγrel
  rcases hEndpointOrientation with hdir | hrev
  · right
    constructor
    · apply Set.Subset.antisymm
      · intro x hx
        have hxw : x = D.vertexPlacement w :=
          common_point_is_attachment hx.1 (by simpa [K] using hx.2)
        simpa [γ, hdir.2] using hxw
      · intro x hx
        have hx_target : x = (D.edgeArc e).target := by
          simpa using hx
        rw [hx_target]
        constructor
        · simpa [γ] using hγtarget_mem
        · simpa [hdir.2] using hAttach_mem
    · simpa [hdir.1] using hLeafEndpoint_notMem
  · left
    constructor
    · apply Set.Subset.antisymm
      · intro x hx
        have hxw : x = D.vertexPlacement w :=
          common_point_is_attachment hx.1 (by simpa [K] using hx.2)
        simpa [γ, hrev.1] using hxw
      · intro x hx
        have hx_source : x = (D.edgeArc e).source := by
          simpa using hx
        rw [hx_source]
        constructor
        · simpa [γ] using hγsource_mem
        · simpa [hrev.1] using hAttach_mem
    · simpa [hrev.2] using hLeafEndpoint_notMem
