import ErdosProblems.Erdos733.ST.PlaneFaceData
import ErdosProblems.Erdos733.ST.CrossingFreeEdgeInteriorDisjoint
import ErdosProblems.Erdos733.ST.PolygonalArcVertexMemCarrier
import Mathlib.Tactic

open Classical
noncomputable section

-- [TABLET NODE: PlaneDartArcLocalGeometry]
lemma PlaneDartArcLocalGeometry {V : Type*} [Fintype V] (G : SimpleGraph V)
    [Fintype G.edgeSet] [DecidableRel G.Adj] (D : OrdinaryPolygonalDrawing G)
    (hD : D.crossingSet.card = 0) (A : PlaneFaceData G D) :
    (∀ d₁ d₂ : G.Dart, d₁.toProd.2 = d₂.toProd.1 → d₁.edge ≠ d₂.edge →
      (A.dartArc d₁).carrier ∩ (A.dartArc d₂).carrier =
        ({D.vertexPlacement d₁.toProd.2} : Set (EuclideanSpace ℝ (Fin 2)))) ∧
      (∀ d₁ d₂ : G.Dart,
        d₁.toProd.1 ≠ d₂.toProd.1 →
          d₁.toProd.1 ≠ d₂.toProd.2 →
            d₁.toProd.2 ≠ d₂.toProd.1 →
              d₁.toProd.2 ≠ d₂.toProd.2 →
                Disjoint (A.dartArc d₁).carrier (A.dartArc d₂).carrier) := by
-- BODY
  classical
  have dartArc_relativeInterior_eq :
      ∀ d : G.Dart,
        (A.dartArc d).relativeInterior = (D.edgeArc (A.dartEdge d)).relativeInterior := by
    intro d
    have hcarrier : (A.dartArc d).carrier = (D.edgeArc (A.dartEdge d)).carrier := by
      simpa using A.dartArc_carrier d
    have hdedge : (A.dartEdge d).1 = s(d.toProd.1, d.toProd.2) := by
      simpa [SimpleGraph.Dart.edge] using A.dartEdge_eq d
    rcases D.edgeArc_endpoints (A.dartEdge d) with ⟨u, v, _huv, huv_edge, hends⟩
    have huv_cases :
        (u = d.toProd.1 ∧ v = d.toProd.2) ∨
          (u = d.toProd.2 ∧ v = d.toProd.1) := by
      have hsym : s(u, v) = s(d.toProd.1, d.toProd.2) := by
        exact huv_edge.symm.trans hdedge
      have hpair :
          (u, v) = d.toProd ∨ (u, v) = d.toProd.swap := by
        simpa [Sym2.eq_iff] using hsym
      rcases hpair with hpair | hpair
      · left
        constructor
        · simpa using congrArg Prod.fst hpair
        · simpa using congrArg Prod.snd hpair
      · right
        constructor
        · simpa using congrArg Prod.fst hpair
        · simpa using congrArg Prod.snd hpair
    have hDendpoints :
        ({(D.edgeArc (A.dartEdge d)).source, (D.edgeArc (A.dartEdge d)).target} :
            Set (EuclideanSpace ℝ (Fin 2))) =
          {D.vertexPlacement d.toProd.1, D.vertexPlacement d.toProd.2} := by
      rcases hends with hdir | hdir
      · rcases hdir with ⟨hsource, htarget⟩
        rcases huv_cases with huv | huv
        · rcases huv with ⟨rfl, rfl⟩
          simp [hsource, htarget]
        · rcases huv with ⟨rfl, rfl⟩
          simp [hsource, htarget, Set.pair_comm]
      · rcases hdir with ⟨hsource, htarget⟩
        rcases huv_cases with huv | huv
        · rcases huv with ⟨rfl, rfl⟩
          simp [hsource, htarget, Set.pair_comm]
        · rcases huv with ⟨rfl, rfl⟩
          simp [hsource, htarget]
    have hdartEndpoints :
        ({(A.dartArc d).source, (A.dartArc d).target} :
            Set (EuclideanSpace ℝ (Fin 2))) =
          {D.vertexPlacement d.toProd.1, D.vertexPlacement d.toProd.2} := by
      simp [A.dartArc_source d, A.dartArc_target d]
    rw [(A.dartArc d).relativeInterior_eq, (D.edgeArc (A.dartEdge d)).relativeInterior_eq,
      hcarrier, hdartEndpoints, ← hDendpoints]
  have endpoint_of_not_rel :
      ∀ (γ : PolygonalArc) {x : EuclideanSpace ℝ (Fin 2)},
        x ∈ γ.carrier → x ∉ γ.relativeInterior → x = γ.source ∨ x = γ.target := by
    intro γ x hxCarrier hxNotRel
    have hxEndpoint : x ∈ ({γ.source, γ.target} :
        Set (EuclideanSpace ℝ (Fin 2))) := by
      by_contra hxNotEndpoint
      exact hxNotRel (by
        rw [γ.relativeInterior_eq]
        exact ⟨hxCarrier, hxNotEndpoint⟩)
    simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hxEndpoint
  have source_mem_carrier : ∀ γ : PolygonalArc, γ.source ∈ γ.carrier := by
    intro γ
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
  have target_mem_carrier : ∀ γ : PolygonalArc, γ.target ∈ γ.carrier := by
    intro γ
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
      exact List.getElem_mem (l := γ.vertices) (n := γ.vertices.length - 1) hlast_lt)
  constructor
  · intro d₁ d₂ hshare hedge_ne
    apply Set.Subset.antisymm
    · intro x hx
      have hx₁ : x ∈ (A.dartArc d₁).carrier := hx.1
      have hx₂ : x ∈ (A.dartArc d₂).carrier := hx.2
      by_cases hx₁rel : x ∈ (A.dartArc d₁).relativeInterior
      · by_cases hx₂rel : x ∈ (A.dartArc d₂).relativeInterior
        · have hedgeA_ne : A.dartEdge d₁ ≠ A.dartEdge d₂ := by
            intro h
            exact hedge_ne (by
              calc
                d₁.edge = (A.dartEdge d₁).1 := (A.dartEdge_eq d₁).symm
                _ = (A.dartEdge d₂).1 := congrArg Subtype.val h
                _ = d₂.edge := A.dartEdge_eq d₂)
          exact False.elim
            (CrossingFreeEdgeInteriorDisjoint G D hD hedgeA_ne
              (by simpa [dartArc_relativeInterior_eq d₁] using hx₁rel)
              (by simpa [dartArc_relativeInterior_eq d₂] using hx₂rel))
        · rcases endpoint_of_not_rel (A.dartArc d₂) hx₂ hx₂rel with hxsrc | hxtgt
          · have hvertex_rel : D.vertexPlacement d₂.toProd.1 ∈
                (D.edgeArc (A.dartEdge d₁)).relativeInterior := by
              simpa [hxsrc, A.dartArc_source d₂, dartArc_relativeInterior_eq d₁] using hx₁rel
            exact False.elim
              (D.no_vertex_in_edge_interior d₂.toProd.1 (A.dartEdge d₁) hvertex_rel)
          · have hvertex_rel : D.vertexPlacement d₂.toProd.2 ∈
                (D.edgeArc (A.dartEdge d₁)).relativeInterior := by
              simpa [hxtgt, A.dartArc_target d₂, dartArc_relativeInterior_eq d₁] using hx₁rel
            exact False.elim
              (D.no_vertex_in_edge_interior d₂.toProd.2 (A.dartEdge d₁) hvertex_rel)
      · rcases endpoint_of_not_rel (A.dartArc d₁) hx₁ hx₁rel with hxsrc | hxtgt
        · by_cases hx₂rel : x ∈ (A.dartArc d₂).relativeInterior
          · have hvertex_rel : D.vertexPlacement d₁.toProd.1 ∈
                (D.edgeArc (A.dartEdge d₂)).relativeInterior := by
              simpa [hxsrc, A.dartArc_source d₁, dartArc_relativeInterior_eq d₂] using hx₂rel
            exact False.elim
              (D.no_vertex_in_edge_interior d₁.toProd.1 (A.dartEdge d₂) hvertex_rel)
          · rcases endpoint_of_not_rel (A.dartArc d₂) hx₂ hx₂rel with hysrc | hytgt
            · have hv : d₁.toProd.1 = d₂.toProd.1 := by
                apply D.vertexPlacement_injective
                calc
                  D.vertexPlacement d₁.toProd.1 = x := by
                    simpa [hxsrc, A.dartArc_source d₁]
                  _ = D.vertexPlacement d₂.toProd.1 := by
                    simpa [hysrc, A.dartArc_source d₂]
              exact False.elim (d₁.fst_ne_snd (by
                calc
                  d₁.toProd.1 = d₂.toProd.1 := hv
                  _ = d₁.toProd.2 := hshare.symm))
            · have hv : d₁.toProd.1 = d₂.toProd.2 := by
                apply D.vertexPlacement_injective
                calc
                  D.vertexPlacement d₁.toProd.1 = x := by
                    simpa [hxsrc, A.dartArc_source d₁]
                  _ = D.vertexPlacement d₂.toProd.2 := by
                    simpa [hytgt, A.dartArc_target d₂]
              have hedge_eq : d₁.edge = d₂.edge := by
                rw [SimpleGraph.Dart.edge, SimpleGraph.Dart.edge]
                calc
                  s(d₁.toProd.1, d₁.toProd.2) = s(d₂.toProd.2, d₂.toProd.1) := by
                    rw [hv, hshare]
                  _ = s(d₂.toProd.1, d₂.toProd.2) := Sym2.eq_swap
              exact False.elim (hedge_ne hedge_eq)
        · by_cases hx₂rel : x ∈ (A.dartArc d₂).relativeInterior
          · have hvertex_rel : D.vertexPlacement d₁.toProd.2 ∈
                (D.edgeArc (A.dartEdge d₂)).relativeInterior := by
              simpa [hxtgt, A.dartArc_target d₁, dartArc_relativeInterior_eq d₂] using hx₂rel
            exact False.elim
              (D.no_vertex_in_edge_interior d₁.toProd.2 (A.dartEdge d₂) hvertex_rel)
          · rcases endpoint_of_not_rel (A.dartArc d₂) hx₂ hx₂rel with hysrc | hytgt
            · have hx_eq : x = D.vertexPlacement d₁.toProd.2 := by
                simpa [hxtgt, A.dartArc_target d₁]
              simpa [hx_eq]
            · have hv : d₁.toProd.2 = d₂.toProd.2 := by
                apply D.vertexPlacement_injective
                calc
                  D.vertexPlacement d₁.toProd.2 = x := by
                    simpa [hxtgt, A.dartArc_target d₁]
                  _ = D.vertexPlacement d₂.toProd.2 := by
                    simpa [hytgt, A.dartArc_target d₂]
              exact False.elim (d₂.fst_ne_snd (by
                calc
                  d₂.toProd.1 = d₁.toProd.2 := hshare.symm
                  _ = d₂.toProd.2 := hv))
    · intro x hx
      have hxv : x = D.vertexPlacement d₁.toProd.2 := by simpa using hx
      rw [hxv]
      constructor
      · simpa [A.dartArc_target d₁] using target_mem_carrier (A.dartArc d₁)
      · simpa [hshare, A.dartArc_source d₂] using source_mem_carrier (A.dartArc d₂)
  · intro d₁ d₂ hff hfs hsf hss
    rw [Set.disjoint_left]
    intro x hx₁ hx₂
    have hedge_ne : A.dartEdge d₁ ≠ A.dartEdge d₂ := by
      intro h
      have hedges : d₁.edge = d₂.edge := by
        calc
          d₁.edge = (A.dartEdge d₁).1 := (A.dartEdge_eq d₁).symm
          _ = (A.dartEdge d₂).1 := congrArg Subtype.val h
          _ = d₂.edge := A.dartEdge_eq d₂
      rcases (SimpleGraph.dart_edge_eq_iff d₁ d₂).mp hedges with hd | hd
      · exact hff (by simpa [hd])
      · exact hfs (by
          calc
            d₁.toProd.1 = d₁.fst := rfl
            _ = d₂.symm.fst := by rw [hd]
            _ = d₂.toProd.2 := rfl)
    by_cases hx₁rel : x ∈ (A.dartArc d₁).relativeInterior
    · by_cases hx₂rel : x ∈ (A.dartArc d₂).relativeInterior
      · exact
          (CrossingFreeEdgeInteriorDisjoint G D hD hedge_ne
            (by simpa [dartArc_relativeInterior_eq d₁] using hx₁rel)
            (by simpa [dartArc_relativeInterior_eq d₂] using hx₂rel))
      · rcases endpoint_of_not_rel (A.dartArc d₂) hx₂ hx₂rel with hxsrc | hxtgt
        · have hvertex_rel : D.vertexPlacement d₂.toProd.1 ∈
              (D.edgeArc (A.dartEdge d₁)).relativeInterior := by
            simpa [hxsrc, A.dartArc_source d₂, dartArc_relativeInterior_eq d₁] using hx₁rel
          exact D.no_vertex_in_edge_interior d₂.toProd.1 (A.dartEdge d₁) hvertex_rel
        · have hvertex_rel : D.vertexPlacement d₂.toProd.2 ∈
              (D.edgeArc (A.dartEdge d₁)).relativeInterior := by
            simpa [hxtgt, A.dartArc_target d₂, dartArc_relativeInterior_eq d₁] using hx₁rel
          exact D.no_vertex_in_edge_interior d₂.toProd.2 (A.dartEdge d₁) hvertex_rel
    · rcases endpoint_of_not_rel (A.dartArc d₁) hx₁ hx₁rel with hxsrc | hxtgt
      · by_cases hx₂rel : x ∈ (A.dartArc d₂).relativeInterior
        · have hvertex_rel : D.vertexPlacement d₁.toProd.1 ∈
              (D.edgeArc (A.dartEdge d₂)).relativeInterior := by
            simpa [hxsrc, A.dartArc_source d₁, dartArc_relativeInterior_eq d₂] using hx₂rel
          exact D.no_vertex_in_edge_interior d₁.toProd.1 (A.dartEdge d₂) hvertex_rel
        · rcases endpoint_of_not_rel (A.dartArc d₂) hx₂ hx₂rel with hysrc | hytgt
          · have hv : d₁.toProd.1 = d₂.toProd.1 := by
              apply D.vertexPlacement_injective
              calc
                D.vertexPlacement d₁.toProd.1 = x := by
                  simpa [hxsrc, A.dartArc_source d₁]
                _ = D.vertexPlacement d₂.toProd.1 := by
                  simpa [hysrc, A.dartArc_source d₂]
            exact hff hv
          · have hv : d₁.toProd.1 = d₂.toProd.2 := by
              apply D.vertexPlacement_injective
              calc
                D.vertexPlacement d₁.toProd.1 = x := by
                  simpa [hxsrc, A.dartArc_source d₁]
                _ = D.vertexPlacement d₂.toProd.2 := by
                  simpa [hytgt, A.dartArc_target d₂]
            exact hfs hv
      · by_cases hx₂rel : x ∈ (A.dartArc d₂).relativeInterior
        · have hvertex_rel : D.vertexPlacement d₁.toProd.2 ∈
              (D.edgeArc (A.dartEdge d₂)).relativeInterior := by
            simpa [hxtgt, A.dartArc_target d₁, dartArc_relativeInterior_eq d₂] using hx₂rel
          exact D.no_vertex_in_edge_interior d₁.toProd.2 (A.dartEdge d₂) hvertex_rel
        · rcases endpoint_of_not_rel (A.dartArc d₂) hx₂ hx₂rel with hysrc | hytgt
          · have hv : d₁.toProd.2 = d₂.toProd.1 := by
              apply D.vertexPlacement_injective
              calc
                D.vertexPlacement d₁.toProd.2 = x := by
                  simpa [hxtgt, A.dartArc_target d₁]
                _ = D.vertexPlacement d₂.toProd.1 := by
                  simpa [hysrc, A.dartArc_source d₂]
            exact hsf hv
          · have hv : d₁.toProd.2 = d₂.toProd.2 := by
              apply D.vertexPlacement_injective
              calc
                D.vertexPlacement d₁.toProd.2 = x := by
                  simpa [hxtgt, A.dartArc_target d₁]
                _ = D.vertexPlacement d₂.toProd.2 := by
                  simpa [hytgt, A.dartArc_target d₂]
            exact hss hv
