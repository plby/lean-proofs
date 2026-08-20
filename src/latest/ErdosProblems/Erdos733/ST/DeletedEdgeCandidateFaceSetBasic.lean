import ErdosProblems.Erdos733.ST.PlaneFaceData
import ErdosProblems.Erdos733.ST.DrawingFaceComponent
import ErdosProblems.Erdos733.ST.OrdinaryDrawingImage
import ErdosProblems.Erdos733.ST.OrdinaryPolygonalDrawing
import ErdosProblems.Erdos733.ST.PolygonalArc
import ErdosProblems.Erdos733.ST.PolygonalSideStrips
import ErdosProblems.Erdos733.ST.DeletedEdgeDrawingImageComplementIdentity
import ErdosProblems.Erdos733.ST.DeletedEdgeLocalIncidentFaces

open Classical
noncomputable section

-- [TABLET NODE: DeletedEdgeCandidateFaceSetBasic]
lemma DeletedEdgeCandidateFaceSetBasic {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet] [DecidableRel G.Adj]
    (D : OrdinaryPolygonalDrawing G) (hD : D.crossingSet.card = 0)
    (A : PlaneFaceData G D) (e : G.edgeFinset)
    (Ddel : OrdinaryPolygonalDrawing (G.deleteEdges {e.1}))
    (hvertex : Ddel.vertexPlacement = D.vertexPlacement)
    (hedges :
      ∀ ed : (G.deleteEdges {e.1}).edgeFinset,
        ∃ eG : G.edgeFinset, eG.1 = ed.1 ∧ eG.1 ≠ e.1 ∧
          Ddel.edgeArc ed = D.edgeArc eG)
    (d : G.Dart) (hd : d.edge = e.1) (FaceDel : Type*)
    (faceDelFintype : Fintype FaceDel)
    (componentOf : Option A.Face → FaceDel)
    (hcomponent_surj : Function.Surjective componentOf)
    (hcomponent_eq :
      ∀ x y : Option A.Face,
        componentOf x = componentOf y ↔
          x = y ∨
            ((x = none ∨ x = some (A.leftFace d) ∨
                x = some (A.leftFace d.symm)) ∧
              (y = none ∨ y = some (A.leftFace d) ∨
                y = some (A.leftFace d.symm))))
    (faceSetDel : FaceDel → Set (EuclideanSpace ℝ (Fin 2)))
    (hfaceSetDel :
      ∀ (Q : FaceDel) (p : EuclideanSpace ℝ (Fin 2)),
        p ∈ faceSetDel Q ↔
          (∃ F : A.Face, componentOf (some F) = Q ∧ p ∈ A.faceSet F) ∨
            (componentOf none = Q ∧ p ∈ (D.edgeArc e).relativeInterior)) :
    ∀ Q : FaceDel,
      (faceSetDel Q).Nonempty ∧
        faceSetDel Q ⊆
          (OrdinaryDrawingImage (G.deleteEdges {e.1}) Ddel)ᶜ ∧
          IsConnected (faceSetDel Q) := by
-- BODY
  classical
  letI : Fintype A.Face := A.faceFintype
  have hdeletedComplementIdentity :
      (OrdinaryDrawingImage (G.deleteEdges {e.1}) Ddel)ᶜ =
          (OrdinaryDrawingImage G D)ᶜ ∪ (D.edgeArc e).relativeInterior :=
    DeletedEdgeDrawingImageComplementIdentity G D hD e Ddel hvertex hedges
  have hdartRelEq :
      ∀ d₀ : G.Dart, d₀.edge = e.1 →
        (A.dartArc d₀).relativeInterior = (D.edgeArc e).relativeInterior := by
    intro d₀ hd₀
    have hdartEdge : A.dartEdge d₀ = e := by
      apply Subtype.ext
      exact (A.dartEdge_eq d₀).trans hd₀
    have hcarrier : (A.dartArc d₀).carrier = (D.edgeArc e).carrier := by
      simpa [hdartEdge] using A.dartArc_carrier d₀
    have hdedge : e.1 = s(d₀.toProd.1, d₀.toProd.2) := by
      simpa [SimpleGraph.Dart.edge] using hd₀.symm
    rcases D.edgeArc_endpoints e with ⟨u, v, _huv, huv_edge, hends⟩
    have huv_cases :
        (u = d₀.toProd.1 ∧ v = d₀.toProd.2) ∨
          (u = d₀.toProd.2 ∧ v = d₀.toProd.1) := by
      have hsym : s(u, v) = s(d₀.toProd.1, d₀.toProd.2) := by
        exact huv_edge.symm.trans hdedge
      have hpair :
          (u, v) = d₀.toProd ∨ (u, v) = d₀.toProd.swap := by
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
        ({(D.edgeArc e).source, (D.edgeArc e).target} :
            Set (EuclideanSpace ℝ (Fin 2))) =
          {D.vertexPlacement d₀.toProd.1, D.vertexPlacement d₀.toProd.2} := by
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
        ({(A.dartArc d₀).source, (A.dartArc d₀).target} :
            Set (EuclideanSpace ℝ (Fin 2))) =
          {D.vertexPlacement d₀.toProd.1, D.vertexPlacement d₀.toProd.2} := by
      simp [A.dartArc_source d₀, A.dartArc_target d₀]
    rw [(A.dartArc d₀).relativeInterior_eq, (D.edgeArc e).relativeInterior_eq,
      hcarrier, hdartEndpoints, ← hDendpoints]
  have hsideFaceClosure :
      ∀ d₀ : G.Dart, d₀.edge = e.1 →
        (D.edgeArc e).relativeInterior ⊆ closure (A.faceSet (A.leftFace d₀)) := by
    intro d₀ hd₀ x hx
    rcases A.sideStripData d₀ with ⟨S, hleft, _hright⟩
    have hxDart : x ∈ (A.dartArc d₀).relativeInterior := by
      simpa [hdartRelEq d₀ hd₀] using hx
    have hxStripClosure : x ∈ closure S.leftStrip :=
      S.relativeInterior_subset_closure_left hxDart
    have hstripFace : S.leftStrip ⊆ A.faceSet (A.leftFace d₀) := by
      rw [← hleft]
      exact A.leftFace_contains d₀
    exact closure_mono hstripFace hxStripClosure
  have hdsymm : d.symm.edge = e.1 := by
    simpa using hd
  have hleftFaceClosure :
      (D.edgeArc e).relativeInterior ⊆ closure (A.faceSet (A.leftFace d)) :=
    hsideFaceClosure d hd
  have hrightFaceClosure :
      (D.edgeArc e).relativeInterior ⊆
        closure (A.faceSet (A.leftFace d.symm)) :=
    hsideFaceClosure d.symm hdsymm
  have hOldComponent :
      ∀ F : A.Face, ComplementComponent (OrdinaryDrawingImage G D) (A.faceSet F) := by
    intro F
    simpa [DrawingFaceComponent] using A.face_component F
  have hOldNonempty : ∀ F : A.Face, (A.faceSet F).Nonempty := fun F =>
    (hOldComponent F).1
  have hOldSubset :
      ∀ F : A.Face, A.faceSet F ⊆ (OrdinaryDrawingImage G D)ᶜ := fun F =>
    (hOldComponent F).2.1
  have hOldConnected : ∀ F : A.Face, IsConnected (A.faceSet F) := fun F =>
    (hOldComponent F).2.2.1
  have hrelNonempty : ((D.edgeArc e).relativeInterior).Nonempty := by
    let γ : PolygonalArc := D.edgeArc e
    have h01 : 0 + 1 < γ.vertices.length := by
      have hlen : 2 ≤ γ.vertices.length := γ.length_ge_two
      omega
    let z : EuclideanSpace ℝ (Fin 2) :=
      midpoint ℝ γ.vertices[0] γ.vertices[0 + 1]
    have hzOpen : z ∈ openSegment ℝ γ.vertices[0] γ.vertices[0 + 1] := by
      simpa [z] using
        (midpoint_mem_openSegment (𝕜 := ℝ) γ.vertices[0] γ.vertices[0 + 1])
    refine ⟨z, ?_⟩
    have hzSeg : z ∈ segment ℝ γ.vertices[0] γ.vertices[0 + 1] :=
      openSegment_subset_segment ℝ γ.vertices[0] γ.vertices[0 + 1] hzOpen
    have hzCarrier : z ∈ γ.carrier := by
      rw [γ.carrier_eq]
      exact ⟨0, h01, hzSeg⟩
    rw [γ.relativeInterior_eq]
    refine ⟨hzCarrier, ?_⟩
    rw [Set.mem_insert_iff, Set.mem_singleton_iff]
    rintro (hz_source | hz_target)
    · have h0lt : 0 < γ.vertices.length := by
        have hlen : 2 ≤ γ.vertices.length := γ.length_ge_two
        omega
      have hsource : γ.vertices[0] = γ.source := by
        have hget : γ.vertices[0]? = some γ.vertices[0] :=
          List.getElem?_eq_getElem h0lt
        rw [← List.head?_eq_getElem?, γ.source_eq_head] at hget
        exact Option.some.inj hget.symm
      have hsource_open : γ.vertices[0] ∈
          openSegment ℝ γ.vertices[0] γ.vertices[0 + 1] := by
        simpa [hsource, hz_source] using hzOpen
      have hne01 : γ.vertices[0] ≠ γ.vertices[0 + 1] := by
        intro hEq
        have hidx : (0 : ℕ) = 0 + 1 :=
          (γ.simple_vertices.getElem_inj_iff).mp hEq
        omega
      exact hne01 ((left_mem_openSegment_iff (𝕜 := ℝ)
        (x := γ.vertices[0]) (y := γ.vertices[0 + 1])).1 hsource_open)
    · let last : ℕ := γ.vertices.length - 1
      have hlast_lt : last < γ.vertices.length := by
        have hlen : 2 ≤ γ.vertices.length := γ.length_ge_two
        dsimp [last]
        omega
      have htarget : γ.vertices[last] = γ.target := by
        have hlastEq := γ.target_eq_last
        rw [List.getLast?_eq_getElem?] at hlastEq
        rw [List.getElem?_eq_getElem hlast_lt] at hlastEq
        exact Option.some.inj hlastEq
      have htarget_open : γ.vertices[last] ∈
          openSegment ℝ γ.vertices[0] γ.vertices[0 + 1] := by
        simpa [htarget, hz_target] using hzOpen
      by_cases hlast_one : last = 0 + 1
      · have htarget_open_right : γ.vertices[0 + 1] ∈
            openSegment ℝ γ.vertices[0] γ.vertices[0 + 1] := by
          convert htarget_open using 2
          exact hlast_one.symm
        have hne01 : γ.vertices[0] ≠ γ.vertices[0 + 1] := by
          intro hEq
          have hidx : (0 : ℕ) = 0 + 1 :=
            (γ.simple_vertices.getElem_inj_iff).mp hEq
          omega
        exact hne01 ((right_mem_openSegment_iff (𝕜 := ℝ)
          (x := γ.vertices[0]) (y := γ.vertices[0 + 1])).1
            htarget_open_right)
      · have hlast_ne_zero : last ≠ 0 := by
          have hlen : 2 ≤ γ.vertices.length := γ.length_ge_two
          dsimp [last]
          omega
        exact γ.vertices_avoid_nonincident_interiors h01 hlast_lt hlast_ne_zero
          hlast_one htarget_open
  have hleftAttachmentConnected :
      IsConnected (A.faceSet (A.leftFace d) ∪
        (D.edgeArc e).relativeInterior) := by
    exact (hOldConnected (A.leftFace d)).subset_closure
      (by
        intro x hx
        exact Or.inl hx)
      (by
        intro x hx
        rcases hx with hxFace | hxRel
        · exact subset_closure hxFace
        · exact hleftFaceClosure hxRel)
  have hrightAttachmentConnected :
      IsConnected (A.faceSet (A.leftFace d.symm) ∪
        (D.edgeArc e).relativeInterior) := by
    exact (hOldConnected (A.leftFace d.symm)).subset_closure
      (by
        intro x hx
        exact Or.inl hx)
      (by
        intro x hx
        rcases hx with hxFace | hxRel
        · exact subset_closure hxFace
        · exact hrightFaceClosure hxRel)
  intro Q
  refine ⟨?_, ?_, ?_⟩
  · rcases hcomponent_surj Q with ⟨atom, hatomQ⟩
    cases atom with
    | none =>
        have hleftQ : componentOf (some (A.leftFace d)) = Q := by
          have hleft_none :
              componentOf (some (A.leftFace d)) = componentOf none := by
            exact (hcomponent_eq (some (A.leftFace d)) none).2
              (Or.inr ⟨Or.inr (Or.inl rfl), Or.inl rfl⟩)
          exact hleft_none.trans hatomQ
        rcases hOldNonempty (A.leftFace d) with ⟨p, hp⟩
        exact ⟨p, (hfaceSetDel Q p).2
          (Or.inl ⟨A.leftFace d, hleftQ, hp⟩)⟩
    | some F =>
        rcases hOldNonempty F with ⟨p, hp⟩
        exact ⟨p, (hfaceSetDel Q p).2 (Or.inl ⟨F, hatomQ, hp⟩)⟩
  · intro p hp
    have hpCases := (hfaceSetDel Q p).1 hp
    rw [hdeletedComplementIdentity]
    rcases hpCases with ⟨F, _hFQ, hpF⟩ | ⟨_hnoneQ, hpRel⟩
    · exact Or.inl (hOldSubset F hpF)
    · exact Or.inr hpRel
  · by_cases hnoneQ : componentOf none = Q
    · have hleftQ : componentOf (some (A.leftFace d)) = Q := by
        have hleft_none :
            componentOf (some (A.leftFace d)) = componentOf none := by
          exact (hcomponent_eq (some (A.leftFace d)) none).2
            (Or.inr ⟨Or.inr (Or.inl rfl), Or.inl rfl⟩)
        exact hleft_none.trans hnoneQ
      have hrightQ : componentOf (some (A.leftFace d.symm)) = Q := by
        have hright_none :
            componentOf (some (A.leftFace d.symm)) = componentOf none := by
          exact (hcomponent_eq (some (A.leftFace d.symm)) none).2
            (Or.inr ⟨Or.inr (Or.inr rfl), Or.inl rfl⟩)
        exact hright_none.trans hnoneQ
      have hstar_eq :
          faceSetDel Q =
            (A.faceSet (A.leftFace d) ∪ (D.edgeArc e).relativeInterior) ∪
              (A.faceSet (A.leftFace d.symm) ∪
                (D.edgeArc e).relativeInterior) := by
        ext p
        constructor
        · intro hp
          rcases (hfaceSetDel Q p).1 hp with ⟨F, hFQ, hpF⟩ | ⟨_hnoneQ, hpRel⟩
          · have hF_none : componentOf (some F) = componentOf none :=
              hFQ.trans hnoneQ.symm
            rcases (hcomponent_eq (some F) none).1 hF_none with hsome_none |
                ⟨hsideF, _hsideNone⟩
            · cases hsome_none
            · rcases hsideF with hF_none' | hF_left | hF_right
              · cases hF_none'
              · have hF_eq : F = A.leftFace d := Option.some.inj hF_left
                exact Or.inl (Or.inl (by simpa [hF_eq] using hpF))
              · have hF_eq : F = A.leftFace d.symm := Option.some.inj hF_right
                exact Or.inr (Or.inl (by simpa [hF_eq] using hpF))
          · exact Or.inl (Or.inr hpRel)
        · intro hp
          rcases hp with (hpLeft | hpRel) | (hpRight | hpRel)
          · exact (hfaceSetDel Q p).2
              (Or.inl ⟨A.leftFace d, hleftQ, hpLeft⟩)
          · exact (hfaceSetDel Q p).2 (Or.inr ⟨hnoneQ, hpRel⟩)
          · exact (hfaceSetDel Q p).2
              (Or.inl ⟨A.leftFace d.symm, hrightQ, hpRight⟩)
          · exact (hfaceSetDel Q p).2 (Or.inr ⟨hnoneQ, hpRel⟩)
      have hmeet :
          ((A.faceSet (A.leftFace d) ∪ (D.edgeArc e).relativeInterior) ∩
            (A.faceSet (A.leftFace d.symm) ∪
              (D.edgeArc e).relativeInterior)).Nonempty := by
        rcases hrelNonempty with ⟨p, hp⟩
        exact ⟨p, Or.inr hp, Or.inr hp⟩
      have hstarConnected :
          IsConnected
            ((A.faceSet (A.leftFace d) ∪ (D.edgeArc e).relativeInterior) ∪
              (A.faceSet (A.leftFace d.symm) ∪
                (D.edgeArc e).relativeInterior)) :=
        IsConnected.union hmeet hleftAttachmentConnected hrightAttachmentConnected
      simpa [hstar_eq] using hstarConnected
    · rcases hcomponent_surj Q with ⟨atom, hatomQ⟩
      cases atom with
      | none =>
          exact (hnoneQ hatomQ).elim
      | some F =>
          have hsingleton_eq : faceSetDel Q = A.faceSet F := by
            ext p
            constructor
            · intro hp
              rcases (hfaceSetDel Q p).1 hp with ⟨F', hF'Q, hpF'⟩ |
                  ⟨hnoneQ', _hpRel⟩
              · have hF'_F :
                    componentOf (some F') = componentOf (some F) :=
                  hF'Q.trans hatomQ.symm
                rcases (hcomponent_eq (some F') (some F)).1 hF'_F with
                    hsome_eq | ⟨hsideF', _hsideF⟩
                · have hF'_eq : F' = F := Option.some.inj hsome_eq
                  simpa [hF'_eq] using hpF'
                · have hnone_F' : componentOf none = componentOf (some F') := by
                    exact (hcomponent_eq none (some F')).2
                      (Or.inr ⟨Or.inl rfl, hsideF'⟩)
                  have hnoneQ' : componentOf none = Q := hnone_F'.trans hF'Q
                  exact (hnoneQ hnoneQ').elim
              · exact (hnoneQ hnoneQ').elim
            · intro hpF
              exact (hfaceSetDel Q p).2 (Or.inl ⟨F, hatomQ, hpF⟩)
          simpa [hsingleton_eq] using hOldConnected F
