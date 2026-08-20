import ErdosProblems.Erdos733.ST.OrdinaryPolygonalDrawing
import ErdosProblems.Erdos733.ST.OrdinaryDrawingImage
import ErdosProblems.Erdos733.ST.PolygonalArcVertexMemCarrier
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Copy

open Classical
noncomputable section

-- [TABLET NODE: PlaneTreeLeafDeletionDrawingData]
lemma PlaneTreeLeafDeletionDrawingData {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet] [DecidableRel G.Adj]
    (D : OrdinaryPolygonalDrawing G) (hD : D.crossingSet.card = 0)
    (hTree : G.IsTree)
    {v w : V} (hvDegree : G.degree v = 1) (hvw_ne : v ≠ w) (hvw : G.Adj v w)
    (hLeaf : ∀ u : V, G.Adj v u → u = w)
    (hDeletedTree : (G.induce ({v}ᶜ : Set V)).IsTree)
    (e : G.edgeFinset) (he : e.1 = Sym2.mk v w) :
    let S : Set V := ({v}ᶜ : Set V)
    ∃ D' : OrdinaryPolygonalDrawing (G.induce S),
      D'.crossingSet.card = 0 ∧
        (∀ x : S, D'.vertexPlacement x = D.vertexPlacement x.1) ∧
          (∀ ed : (G.induce S).edgeFinset,
            ∃ eG : G.edgeFinset,
              eG.1 = Sym2.map (Subtype.val : S → V) ed.1 ∧
                eG.1 ≠ e.1 ∧
                  D'.edgeArc ed = D.edgeArc eG) ∧
            OrdinaryDrawingImage G D =
              OrdinaryDrawingImage (G.induce S) D' ∪ (D.edgeArc e).carrier ∧
            D.vertexPlacement w ∈ OrdinaryDrawingImage (G.induce S) D' ∧
            D.vertexPlacement v ∉ OrdinaryDrawingImage (G.induce S) D' ∧
            (G.induce S).edgeFinset.card < G.edgeFinset.card ∧
              (((D.edgeArc e).source = D.vertexPlacement v ∧
                  (D.edgeArc e).target = D.vertexPlacement w) ∨
                ((D.edgeArc e).source = D.vertexPlacement w ∧
                  (D.edgeArc e).target = D.vertexPlacement v)) := by
-- BODY
  classical
  intro S
  have induce_coe :
      (⇑(SimpleGraph.Embedding.induce (G := G) S) : S → V) = Subtype.val := rfl
  have induce_toHom_coe :
      (⇑(SimpleGraph.Embedding.induce (G := G) S).toHom : S → V) = Subtype.val := rfl
  let oldEdge : (G.induce S).edgeFinset → G.edgeFinset := fun ed =>
    ⟨Sym2.map (Subtype.val : S → V) ed.1, by
      exact SimpleGraph.mem_edgeFinset.mpr (by
        simpa only [induce_toHom_coe] using
          (SimpleGraph.Embedding.induce (G := G) S).toHom.map_mem_edgeSet
            (SimpleGraph.mem_edgeFinset.mp ed.2))⟩
  have oldEdge_val :
      ∀ ed : (G.induce S).edgeFinset,
        (oldEdge ed).1 = Sym2.map (Subtype.val : S → V) ed.1 := by
    intro ed
    rfl
  have oldEdge_endpoint_mem :
      ∀ (ed : (G.induce S).edgeFinset) {u : V},
        u ∈ (oldEdge ed).1 → u ∈ S := by
    intro ed u hu
    rw [oldEdge_val ed] at hu
    rcases Sym2.mem_map.mp hu with ⟨a, _ha, rfl⟩
    exact a.2
  have oldEdge_ne_deleted :
      ∀ ed : (G.induce S).edgeFinset, (oldEdge ed).1 ≠ e.1 := by
    intro ed hdel
    have hv_old : v ∈ (oldEdge ed).1 := by
      rw [hdel, he]
      simp [Sym2.mem_iff]
    have hvS : v ∈ S := oldEdge_endpoint_mem ed hv_old
    exact hvS (by simp [S])
  have oldEdge_injective : Function.Injective oldEdge := by
    intro ed₁ ed₂ h
    apply Subtype.ext
    apply Sym2.map.injective (Subtype.val_injective : Function.Injective (Subtype.val : S → V))
    simpa [oldEdge_val] using congrArg Subtype.val h
  let D' : OrdinaryPolygonalDrawing (G.induce S) :=
    { vertexPlacement := fun x : S => D.vertexPlacement x.1
      vertexPlacement_injective := by
        intro x y hxy
        apply Subtype.ext
        exact D.vertexPlacement_injective hxy
      edgeArc := fun ed => D.edgeArc (oldEdge ed)
      edgeArc_endpoints := by
        intro ed
        rcases D.edgeArc_endpoints (oldEdge ed) with ⟨a, b, hab, hedge, hends⟩
        have haS : a ∈ S := by
          exact oldEdge_endpoint_mem ed (by rw [hedge]; simp [Sym2.mem_iff])
        have hbS : b ∈ S := by
          exact oldEdge_endpoint_mem ed (by rw [hedge]; simp [Sym2.mem_iff])
        refine ⟨⟨a, haS⟩, ⟨b, hbS⟩, ?_, ?_, ?_⟩
        · simpa using hab
        · apply (Sym2.map.injective
            (Subtype.val_injective : Function.Injective (Subtype.val : S → V)))
          simpa [oldEdge_val ed] using hedge
        · simpa using hends
      crossingSet := ∅
      no_vertex_in_edge_interior := by
        intro x ed
        exact D.no_vertex_in_edge_interior x.1 (oldEdge ed)
      no_three_edge_interiors_meet := by
        intro ed₁ ed₂ ed₃ p h₁₂ h₁₃ h₂₃ hp₁ hp₂ hp₃
        exact D.no_three_edge_interiors_meet
          (oldEdge_injective.ne h₁₂) (oldEdge_injective.ne h₁₃)
          (oldEdge_injective.ne h₂₃) hp₁ hp₂ hp₃
      transverse_intersections := by
        intro ed₁ ed₂ p h₁₂ hp₁ hp₂
        exact D.transverse_intersections (oldEdge_injective.ne h₁₂) hp₁ hp₂
      no_shared_nondegenerate_subarc := by
        intro ed₁ ed₂ h₁₂
        exact D.no_shared_nondegenerate_subarc (oldEdge_injective.ne h₁₂)
      crossingSet_spec := by
        intro p
        constructor
        · intro hp
          simpa using hp
        · rintro ⟨ed₁, ed₂, h₁₂, hp₁, hp₂⟩
          have hpOld : p ∈ D.crossingSet :=
            (D.crossingSet_spec p).2
              ⟨oldEdge ed₁, oldEdge ed₂, oldEdge_injective.ne h₁₂, hp₁, hp₂⟩
          have hDempty : D.crossingSet = ∅ := Finset.card_eq_zero.mp hD
          exfalso
          simpa [hDempty] using hpOld
      adjacentEdgeCrossingCount := 0
      adjacentEdgeCrossingCount_eq := by
        simp }
  have hD'_crossing : D'.crossingSet.card = 0 := by
    simp [D']
  have hD'_vertex : ∀ x : S, D'.vertexPlacement x = D.vertexPlacement x.1 := by
    intro x
    rfl
  have hD'_edges :
      ∀ ed : (G.induce S).edgeFinset,
        ∃ eG : G.edgeFinset,
          eG.1 = Sym2.map (Subtype.val : S → V) ed.1 ∧
            eG.1 ≠ e.1 ∧
              D'.edgeArc ed = D.edgeArc eG := by
    intro ed
    exact ⟨oldEdge ed, oldEdge_val ed, oldEdge_ne_deleted ed, rfl⟩
  have hEdgeClass :
      ∀ f : G.edgeFinset, f = e ∨
        ∃ ed : (G.induce S).edgeFinset, oldEdge ed = f := by
    intro f
    by_cases hvf : v ∈ (f : Sym2 V)
    · left
      let u : V := Sym2.Mem.other hvf
      have hf_eq : (f : Sym2 V) = Sym2.mk v u := by
        exact (Sym2.other_spec hvf).symm
      have hvu : G.Adj v u := by
        rw [← SimpleGraph.mem_edgeSet]
        simpa [hf_eq] using (SimpleGraph.mem_edgeFinset.mp f.2)
      have hu : u = w := hLeaf u hvu
      apply Subtype.ext
      simpa [hf_eq, hu] using he.symm
    · right
      have hmemS : ∀ a ∈ (f : Sym2 V), a ∈ S := by
        intro a ha
        exact fun hav => hvf (hav ▸ ha)
      let edSym : Sym2 S :=
        (f : Sym2 V).pmap (fun a ha => (⟨a, ha⟩ : S)) hmemS
      have hedSym_map : Sym2.map (Subtype.val : S → V) edSym = f.1 := by
        rw [Sym2.pmap_subtype_map_subtypeVal]
      have hedSym_mem : edSym ∈ (G.induce S).edgeSet := by
        apply ((SimpleGraph.Embedding.induce (G := G) S).map_mem_edgeSet_iff).mp
        rw [induce_coe, hedSym_map]
        exact SimpleGraph.mem_edgeFinset.mp f.2
      let ed : (G.induce S).edgeFinset :=
        ⟨edSym, SimpleGraph.mem_edgeFinset.mpr hedSym_mem⟩
      refine ⟨ed, ?_⟩
      apply Subtype.ext
      simpa [ed, oldEdge_val, hedSym_map]
  have hArcSourceMem :
      ∀ γ : PolygonalArc, γ.source ∈ γ.carrier := by
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
  have hArcTargetMem :
      ∀ γ : PolygonalArc, γ.target ∈ γ.carrier := by
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
      exact
        List.getElem_mem (l := γ.vertices) (n := γ.vertices.length - 1) hlast_lt)
  have hEndpointOrientation :
      (((D.edgeArc e).source = D.vertexPlacement v ∧
          (D.edgeArc e).target = D.vertexPlacement w) ∨
        ((D.edgeArc e).source = D.vertexPlacement w ∧
          (D.edgeArc e).target = D.vertexPlacement v)) := by
    rcases D.edgeArc_endpoints e with ⟨a, b, _hab, hedge, hends⟩
    have hmk : Sym2.mk a b = Sym2.mk v w := by
      exact hedge.symm.trans he
    rw [Sym2.eq_iff] at hmk
    rcases hmk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hends
    · rcases hends with hdir | hdir
      · right
        exact hdir
      · left
        exact hdir
  have hDv_mem_e : D.vertexPlacement v ∈ (D.edgeArc e).carrier := by
    rcases hEndpointOrientation with hdir | hdir
    · exact hdir.1 ▸ hArcSourceMem (D.edgeArc e)
    · exact hdir.2 ▸ hArcTargetMem (D.edgeArc e)
  have hImage :
      OrdinaryDrawingImage G D =
        OrdinaryDrawingImage (G.induce S) D' ∪ (D.edgeArc e).carrier := by
    ext x
    constructor
    · intro hx
      rw [OrdinaryDrawingImage] at hx ⊢
      rcases hx with hxv | hxe
      · rcases hxv with ⟨u, rfl⟩
        by_cases huv : u = v
        · right
          simpa [huv] using hDv_mem_e
        · left
          left
          exact ⟨⟨u, by simpa [S] using huv⟩, rfl⟩
      · rcases Set.mem_iUnion.mp hxe with ⟨f, hxf⟩
        rcases hEdgeClass f with rfl | ⟨ed, hed⟩
        · right
          exact hxf
        · left
          right
          refine Set.mem_iUnion.mpr ⟨ed, ?_⟩
          simpa [D', hed] using hxf
    · intro hx
      rw [OrdinaryDrawingImage] at hx ⊢
      rcases hx with hxNew | hxe
      · rcases hxNew with hxv | hxed
        · left
          rcases hxv with ⟨u, hxu⟩
          exact ⟨u.1, hxu⟩
        · right
          rcases Set.mem_iUnion.mp hxed with ⟨ed, hxed⟩
          refine Set.mem_iUnion.mpr ⟨oldEdge ed, ?_⟩
          simpa [D'] using hxed
      · right
        exact Set.mem_iUnion.mpr ⟨e, hxe⟩
  have hW_mem_image :
      D.vertexPlacement w ∈ OrdinaryDrawingImage (G.induce S) D' := by
    rw [OrdinaryDrawingImage]
    left
    exact ⟨⟨w, by simpa [S] using hvw_ne.symm⟩, rfl⟩
  have endpoint_of_not_rel :
      ∀ (γ : PolygonalArc) ⦃y : EuclideanSpace ℝ (Fin 2)⦄,
        y ∈ γ.carrier → y ∉ γ.relativeInterior →
          y = γ.source ∨ y = γ.target := by
    intro γ y hy hnot
    have hyEnd : y ∈ ({γ.source, γ.target} : Set (EuclideanSpace ℝ (Fin 2))) := by
      by_contra hnotEnd
      have hyRel : y ∈ γ.relativeInterior := by
        rw [γ.relativeInterior_eq]
        exact ⟨hy, hnotEnd⟩
      exact hnot hyRel
    simpa using hyEnd
  have hV_not_image :
      D.vertexPlacement v ∉ OrdinaryDrawingImage (G.induce S) D' := by
    intro hvimg
    rw [OrdinaryDrawingImage] at hvimg
    rcases hvimg with hvVertex | hvEdge
    · rcases hvVertex with ⟨u, huv⟩
      have huv' : D.vertexPlacement u.1 = D.vertexPlacement v := by
        simpa using huv
      have hu_eq_v : u.1 = v := D.vertexPlacement_injective huv'
      exact u.2 (by simpa [S, hu_eq_v])
    · rcases Set.mem_iUnion.mp hvEdge with ⟨ed, hvCarrier⟩
      by_cases hvRel : D.vertexPlacement v ∈ (D.edgeArc (oldEdge ed)).relativeInterior
      · exact D.no_vertex_in_edge_interior v (oldEdge ed) hvRel
      · have hvEnd := endpoint_of_not_rel (D.edgeArc (oldEdge ed)) hvCarrier hvRel
        rcases D.edgeArc_endpoints (oldEdge ed) with ⟨a, b, _hab, hedge, hends⟩
        have haS : a ∈ S := by
          exact oldEdge_endpoint_mem ed (by rw [hedge]; simp [Sym2.mem_iff])
        have hbS : b ∈ S := by
          exact oldEdge_endpoint_mem ed (by rw [hedge]; simp [Sym2.mem_iff])
        rcases hvEnd with hvsrc | hvtgt
        · rcases hends with hdir | hrev
          · have hplace : D.vertexPlacement v = D.vertexPlacement a := by
              rw [hvsrc, hdir.1]
            have h_eq : v = a := D.vertexPlacement_injective hplace
            exact haS (by simpa [S] using h_eq.symm)
          · have hplace : D.vertexPlacement v = D.vertexPlacement b := by
              rw [hvsrc, hrev.1]
            have h_eq : v = b := D.vertexPlacement_injective hplace
            exact hbS (by simpa [S] using h_eq.symm)
        · rcases hends with hdir | hrev
          · have hplace : D.vertexPlacement v = D.vertexPlacement b := by
              rw [hvtgt, hdir.2]
            have h_eq : v = b := D.vertexPlacement_injective hplace
            exact hbS (by simpa [S] using h_eq.symm)
          · have hplace : D.vertexPlacement v = D.vertexPlacement a := by
              rw [hvtgt, hrev.2]
            have h_eq : v = a := D.vertexPlacement_injective hplace
            exact haS (by simpa [S] using h_eq.symm)
  have hEdgeDecrease : (G.induce S).edgeFinset.card < G.edgeFinset.card := by
    have hGcard : G.edgeFinset.card + 1 = Fintype.card V := hTree.card_edgeFinset
    have hDelcard : (G.induce ({v}ᶜ : Set V)).edgeFinset.card + 1 =
        Fintype.card ({v}ᶜ : Set V) := hDeletedTree.card_edgeFinset
    have hScard_lt : Fintype.card ({v}ᶜ : Set V) < Fintype.card V :=
      Fintype.card_subtype_lt
        (p := fun x : V => x ∈ ({v}ᶜ : Set V)) (x := v) (by simp)
    change (G.induce ({v}ᶜ : Set V)).edgeFinset.card < G.edgeFinset.card
    omega
  exact ⟨D', hD'_crossing, hD'_vertex, hD'_edges, hImage, hW_mem_image,
    hV_not_image, hEdgeDecrease, hEndpointOrientation⟩
