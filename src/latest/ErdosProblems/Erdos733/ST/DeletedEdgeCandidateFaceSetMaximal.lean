import ErdosProblems.Erdos733.ST.DeletedEdgeCandidateFaceSetBasic
import ErdosProblems.Erdos733.ST.DeletedEdgePathAtomClassification
import ErdosProblems.Erdos733.ST.OpenConnectedComponentPolygonallyConnected
import ErdosProblems.Erdos733.ST.OrdinaryDrawingImageCompact

open Classical
noncomputable section

-- [TABLET NODE: DeletedEdgeCandidateFaceSetMaximal]
lemma DeletedEdgeCandidateFaceSetMaximal {V : Type*} [Fintype V]
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
    ∀ (Q : FaceDel) (C : Set (EuclideanSpace ℝ (Fin 2))),
      C.Nonempty →
        C ⊆ (OrdinaryDrawingImage (G.deleteEdges {e.1}) Ddel)ᶜ →
          IsConnected C →
            faceSetDel Q ⊆ C →
              C ⊆ faceSetDel Q := by
-- BODY
  classical
  let E := EuclideanSpace ℝ (Fin 2)
  let Udel : Set E := (OrdinaryDrawingImage (G.deleteEdges {e.1}) Ddel)ᶜ
  let Uold : Set E := (OrdinaryDrawingImage G D)ᶜ
  let rel : Set E := (D.edgeArc e).relativeInterior
  have hdeletedComplementIdentity : Udel = Uold ∪ rel := by
    dsimp [Udel, Uold, rel]
    exact DeletedEdgeDrawingImageComplementIdentity G D hD e Ddel hvertex hedges
  have hBasic :
      ∀ Q : FaceDel,
        (faceSetDel Q).Nonempty ∧ faceSetDel Q ⊆ Udel ∧
          IsConnected (faceSetDel Q) := by
    intro Q
    simpa [Udel] using
      DeletedEdgeCandidateFaceSetBasic G D hD A e Ddel hvertex hedges d hd
        FaceDel faceDelFintype componentOf hcomponent_surj hcomponent_eq
        faceSetDel hfaceSetDel Q
  have hOldComponent :
      ∀ F : A.Face, ComplementComponent (OrdinaryDrawingImage G D) (A.faceSet F) := by
    intro F
    simpa [DrawingFaceComponent] using A.face_component F
  have hOldSubset : ∀ F : A.Face, A.faceSet F ⊆ Uold := by
    intro F
    exact (hOldComponent F).2.1
  have hOldConnected : ∀ F : A.Face, IsConnected (A.faceSet F) := by
    intro F
    exact (hOldComponent F).2.2.1
  have hOldMaximal :
      ∀ F : A.Face, ∀ C : Set E,
        C.Nonempty → C ⊆ Uold → IsConnected C → A.faceSet F ⊆ C →
          C ⊆ A.faceSet F := by
    intro F
    exact (hOldComponent F).2.2.2
  have hUoldOpen : IsOpen Uold := by
    dsimp [Uold]
    exact (OrdinaryDrawingImageCompact G D).isClosed.isOpen_compl
  have hFaceOpen : ∀ F : A.Face, IsOpen (A.faceSet F) := by
    intro F
    rw [Metric.isOpen_iff]
    intro p hpF
    have hpOld : p ∈ Uold := hOldSubset F hpF
    rcases Metric.isOpen_iff.mp hUoldOpen p hpOld with ⟨r, hrpos, hball⟩
    refine ⟨r, hrpos, ?_⟩
    intro z hz
    have hpBall : p ∈ Metric.ball p r := by
      simpa using hrpos
    have hsegBall : segment ℝ p z ⊆ Metric.ball p r := by
      intro q hq
      exact (convex_ball p r).segment_subset hpBall hz hq
    have hsegOld : segment ℝ p z ⊆ Uold := by
      intro q hq
      exact hball (hsegBall hq)
    have hsegConnected : IsConnected (segment ℝ p z) :=
      (convex_segment p z).isConnected ⟨p, left_mem_segment ℝ p z⟩
    have hmeet : (A.faceSet F ∩ segment ℝ p z).Nonempty :=
      ⟨p, hpF, left_mem_segment ℝ p z⟩
    have hUnionConnected : IsConnected (A.faceSet F ∪ segment ℝ p z) :=
      IsConnected.union hmeet (hOldConnected F) hsegConnected
    have hUnionSubsetOld : A.faceSet F ∪ segment ℝ p z ⊆ Uold := by
      intro q hq
      rcases hq with hqF | hqSeg
      · exact hOldSubset F hqF
      · exact hsegOld hqSeg
    have hUnionNonempty : (A.faceSet F ∪ segment ℝ p z).Nonempty :=
      ⟨p, Or.inl hpF⟩
    have hFaceSubsetUnion : A.faceSet F ⊆ A.faceSet F ∪ segment ℝ p z := by
      intro q hq
      exact Or.inl hq
    have hUnionSubsetFace :
        A.faceSet F ∪ segment ℝ p z ⊆ A.faceSet F :=
      hOldMaximal F (A.faceSet F ∪ segment ℝ p z) hUnionNonempty
        hUnionSubsetOld hUnionConnected hFaceSubsetUnion
    exact hUnionSubsetFace (Or.inr (right_mem_segment ℝ p z))
  have hRelSubsetImage : rel ⊆ OrdinaryDrawingImage G D := by
    intro p hp
    rw [OrdinaryDrawingImage]
    right
    refine Set.mem_iUnion.mpr ⟨e, ?_⟩
    have hpCarrier : p ∈ (D.edgeArc e).carrier := by
      have hpRel : p ∈ (D.edgeArc e).relativeInterior := by
        simpa [rel] using hp
      rw [(D.edgeArc e).relativeInterior_eq] at hpRel
      exact hpRel.1
    exact hpCarrier
  have hRelDisjointFace :
      ∀ F : A.Face, Disjoint rel (A.faceSet F) := by
    intro F
    rw [Set.disjoint_left]
    intro p hpRel hpF
    exact (hOldSubset F hpF) (hRelSubsetImage hpRel)
  have hFaceUnique :
      ∀ {p : E} {F F' : A.Face}, p ∈ A.faceSet F → p ∈ A.faceSet F' →
        F = F' := by
    intro p F F' hpF hpF'
    rcases A.complement_point_face p (hOldSubset F hpF) with
      ⟨F0, _hpF0, huniq⟩
    have hF : F = F0 := huniq F hpF
    have hF' : F' = F0 := huniq F' hpF'
    exact hF.trans hF'.symm
  have hCandidateUnique :
      ∀ {p : E} {Q Q' : FaceDel}, p ∈ faceSetDel Q → p ∈ faceSetDel Q' →
        Q = Q' := by
    intro p Q Q' hpQ hpQ'
    rcases (hfaceSetDel Q p).1 hpQ with ⟨F, hFQ, hpF⟩ | ⟨hnoneQ, hpRel⟩
    · rcases (hfaceSetDel Q' p).1 hpQ' with
        ⟨F', hF'Q', hpF'⟩ | ⟨hnoneQ', hpRel'⟩
      · have hFF' : F = F' := hFaceUnique hpF hpF'
        subst hFF'
        exact hFQ.symm.trans hF'Q'
      · exact False.elim
          ((Set.disjoint_left.mp (hRelDisjointFace F)) hpRel' hpF)
    · rcases (hfaceSetDel Q' p).1 hpQ' with
        ⟨F', hF'Q', hpF'⟩ | ⟨hnoneQ', _hpRel'⟩
      · exact False.elim
          ((Set.disjoint_left.mp (hRelDisjointFace F')) hpRel hpF')
      · exact hnoneQ.symm.trans hnoneQ'
  have hCoverUdel :
      ∀ p : E, p ∈ Udel → ∃ Q : FaceDel, p ∈ faceSetDel Q := by
    intro p hp
    have hpCases : p ∈ Uold ∪ rel := by
      simpa [hdeletedComplementIdentity] using hp
    rcases hpCases with hpOld | hpRel
    · rcases A.complement_point_face p hpOld with ⟨F, hpF, _huniq⟩
      exact ⟨componentOf (some F),
        (hfaceSetDel (componentOf (some F)) p).2 (Or.inl ⟨F, rfl, hpF⟩)⟩
    · exact ⟨componentOf none,
        (hfaceSetDel (componentOf none) p).2 (Or.inr ⟨rfl, hpRel⟩)⟩
  let RelOpenInUdel : Set E → Prop :=
    fun S => ∀ p : E, p ∈ S →
      ∃ N : Set E, IsOpen N ∧ p ∈ N ∧ N ∩ Udel ⊆ S
  have hCandidateRelOpen : ∀ Q : FaceDel, RelOpenInUdel (faceSetDel Q) := by
    intro Q p hp
    rcases (hfaceSetDel Q p).1 hp with ⟨F, hFQ, hpF⟩ | ⟨hnoneQ, hpRel⟩
    · refine ⟨A.faceSet F, hFaceOpen F, hpF, ?_⟩
      intro z hz
      exact (hfaceSetDel Q z).2 (Or.inl ⟨F, hFQ, hz.1⟩)
    · rcases DeletedEdgeLocalIncidentFaces G D hD A e d hd p hpRel with
        ⟨N, hNopen, hpN, hNsubset⟩
      refine ⟨N, hNopen, hpN, ?_⟩
      intro z hz
      rcases hz with ⟨hzN, hzUdel⟩
      have hzCases : z ∈ Uold ∪ rel := by
        simpa [hdeletedComplementIdentity] using hzUdel
      rcases hzCases with hzOld | hzRel
      · have hzSide :
            z ∈ A.faceSet (A.leftFace d) ∪ A.faceSet (A.leftFace d.symm) :=
          hNsubset ⟨hzN, hzOld⟩
        rcases hzSide with hzLeft | hzRight
        · have hleftQ : componentOf (some (A.leftFace d)) = Q := by
            have hleft_none :
                componentOf (some (A.leftFace d)) = componentOf none := by
              exact (hcomponent_eq (some (A.leftFace d)) none).2
                (Or.inr ⟨Or.inr (Or.inl rfl), Or.inl rfl⟩)
            exact hleft_none.trans hnoneQ
          exact (hfaceSetDel Q z).2
            (Or.inl ⟨A.leftFace d, hleftQ, hzLeft⟩)
        · have hrightQ : componentOf (some (A.leftFace d.symm)) = Q := by
            have hright_none :
                componentOf (some (A.leftFace d.symm)) = componentOf none := by
              exact (hcomponent_eq (some (A.leftFace d.symm)) none).2
                (Or.inr ⟨Or.inr (Or.inr rfl), Or.inl rfl⟩)
            exact hright_none.trans hnoneQ
          exact (hfaceSetDel Q z).2
            (Or.inl ⟨A.leftFace d.symm, hrightQ, hzRight⟩)
      · exact (hfaceSetDel Q z).2 (Or.inr ⟨hnoneQ, hzRel⟩)
  let OpenHull : Set E → Set E :=
    fun S => {z : E | ∃ p : E, p ∈ S ∧
      ∃ N : Set E, IsOpen N ∧ p ∈ N ∧ N ∩ Udel ⊆ S ∧ z ∈ N}
  have hOpenHullOpen : ∀ S : Set E, IsOpen (OpenHull S) := by
    intro S
    rw [isOpen_iff_forall_mem_open]
    intro z hz
    rcases hz with ⟨p, hpS, N, hNopen, hpN, hNsub, hzN⟩
    refine ⟨N, ?_, hNopen, hzN⟩
    intro y hyN
    exact ⟨p, hpS, N, hNopen, hpN, hNsub, hyN⟩
  have hOpenHullMem :
      ∀ S : Set E, RelOpenInUdel S → S ⊆ OpenHull S := by
    intro S hrelS p hpS
    rcases hrelS p hpS with ⟨N, hNopen, hpN, hNsub⟩
    exact ⟨p, hpS, N, hNopen, hpN, hNsub, hpN⟩
  have hOpenHullSub :
      ∀ S : Set E, OpenHull S ∩ Udel ⊆ S := by
    intro S z hz
    rcases hz with ⟨hzHull, hzUdel⟩
    rcases hzHull with ⟨p, hpS, N, hNopen, hpN, hNsub, hzN⟩
    exact hNsub ⟨hzN, hzUdel⟩
  intro Q C _hCne hCsub hCconn hQC p hpC
  by_contra hpNotQ
  let Other : Set E := {x : E | ∃ Q' : FaceDel, Q' ≠ Q ∧ x ∈ faceSetDel Q'}
  have hOtherRelOpen : RelOpenInUdel Other := by
    intro x hx
    rcases hx with ⟨Q', hQ'ne, hxQ'⟩
    rcases hCandidateRelOpen Q' x hxQ' with ⟨N, hNopen, hxN, hNsub⟩
    refine ⟨N, hNopen, hxN, ?_⟩
    intro z hz
    exact ⟨Q', hQ'ne, hNsub hz⟩
  let Rset : Set E := OpenHull (faceSetDel Q)
  let Nset : Set E := OpenHull Other
  have hRopen : IsOpen Rset := by
    dsimp [Rset]
    exact hOpenHullOpen (faceSetDel Q)
  have hNopen : IsOpen Nset := by
    dsimp [Nset]
    exact hOpenHullOpen Other
  have hcover : C ⊆ Rset ∪ Nset := by
    intro x hxC
    rcases hCoverUdel x (hCsub hxC) with ⟨Qx, hxQx⟩
    by_cases hQx : Qx = Q
    · left
      dsimp [Rset]
      exact hOpenHullMem (faceSetDel Q) (hCandidateRelOpen Q)
        (by simpa [hQx] using hxQx)
    · right
      dsimp [Nset, Other]
      exact hOpenHullMem Other hOtherRelOpen ⟨Qx, hQx, hxQx⟩
  have hRnonempty : (C ∩ Rset).Nonempty := by
    rcases (hBasic Q).1 with ⟨q, hqQ⟩
    refine ⟨q, hQC hqQ, ?_⟩
    dsimp [Rset]
    exact hOpenHullMem (faceSetDel Q) (hCandidateRelOpen Q) hqQ
  have hNnonempty : (C ∩ Nset).Nonempty := by
    have hpUdel : p ∈ Udel := hCsub hpC
    rcases hCoverUdel p hpUdel with ⟨Qp, hpQp⟩
    have hQp_ne : Qp ≠ Q := by
      intro hQp
      exact hpNotQ (by simpa [hQp] using hpQp)
    refine ⟨p, hpC, ?_⟩
    dsimp [Nset, Other]
    exact hOpenHullMem Other hOtherRelOpen ⟨Qp, hQp_ne, hpQp⟩
  have hinter :
      (C ∩ (Rset ∩ Nset)).Nonempty :=
    hCconn.isPreconnected Rset Nset hRopen hNopen hcover hRnonempty hNnonempty
  rcases hinter with ⟨x, hxC, hxR, hxN⟩
  have hxUdel : x ∈ Udel := hCsub hxC
  have hxQ : x ∈ faceSetDel Q := by
    exact hOpenHullSub (faceSetDel Q) ⟨by simpa [Rset] using hxR, hxUdel⟩
  have hxOther : x ∈ Other := by
    exact hOpenHullSub Other ⟨by simpa [Nset] using hxN, hxUdel⟩
  rcases hxOther with ⟨Q', hQ'ne, hxQ'⟩
  exact hQ'ne (hCandidateUnique hxQ' hxQ)
