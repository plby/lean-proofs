import Util.IncidenceGeometry.DeletedEdgeCandidateFaceSetBasic
import Util.IncidenceGeometry.DeletedEdgeCandidateFaceSetMaximal
import Util.IncidenceGeometry.DeletedEdgeDrawingImageComplementIdentity
import Util.IncidenceGeometry.DeletedEdgePathAtomClassification
import Util.IncidenceGeometry.DrawingFaceComponent
import Util.IncidenceGeometry.OrdinaryDrawingImageCompact
import Util.IncidenceGeometry.OpenConnectedComponentPolygonallyConnected

open Classical
noncomputable section

lemma DeletedEdgeCandidateFacesComplete {V : Type*} [Fintype V]
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
    ∀ C : Set (EuclideanSpace ℝ (Fin 2)),
      DrawingFaceComponent (G.deleteEdges {e.1}) Ddel C →
        ∃! Q : FaceDel, faceSetDel Q = C := by
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
  have hCandidateMaximal :
      ∀ (Q : FaceDel) (C : Set E),
        C.Nonempty →
          C ⊆ Udel →
            IsConnected C →
              faceSetDel Q ⊆ C →
                C ⊆ faceSetDel Q := by
    intro Q C hCne hCsub hCconn hQC
    simpa [Udel] using
      DeletedEdgeCandidateFaceSetMaximal G D hD A e Ddel hvertex hedges d hd
        FaceDel faceDelFintype componentOf hcomponent_surj hcomponent_eq
        faceSetDel hfaceSetDel Q C hCne hCsub hCconn hQC
  have hOldComponent :
      ∀ F : A.Face, ComplementComponent (OrdinaryDrawingImage G D) (A.faceSet F) := by
    intro F
    simpa [DrawingFaceComponent] using A.face_component F
  have hOldSubset : ∀ F : A.Face, A.faceSet F ⊆ Uold := by
    intro F
    exact (hOldComponent F).2.1
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
        (hfaceSetDel (componentOf (some F)) p).2
          (Or.inl ⟨F, rfl, hpF⟩)⟩
    · exact ⟨componentOf none,
        (hfaceSetDel (componentOf none) p).2 (Or.inr ⟨rfl, hpRel⟩)⟩
  intro C hC
  have hComp :
      ComplementComponent (OrdinaryDrawingImage (G.deleteEdges {e.1}) Ddel) C := by
    simpa [DrawingFaceComponent] using hC
  have hCne : C.Nonempty := hComp.1
  have hCsub : C ⊆ Udel := by
    simpa [Udel] using hComp.2.1
  have hCconn : IsConnected C := hComp.2.2.1
  rcases hComp.1 with ⟨p0, hp0C⟩
  rcases hCoverUdel p0 (hCsub hp0C) with ⟨Q, hp0Q⟩
  refine ⟨Q, ?_, ?_⟩
  · have hQsubC : faceSetDel Q ⊆ C := by
      have hInter : (C ∩ faceSetDel Q).Nonempty := ⟨p0, hp0C, hp0Q⟩
      have hUnionConnected : IsConnected (C ∪ faceSetDel Q) :=
        IsConnected.union hInter hCconn (hBasic Q).2.2
      have hUnionSubset : C ∪ faceSetDel Q ⊆ Udel := by
        intro p hp
        rcases hp with hpC | hpQ
        · exact hCsub hpC
        · exact (hBasic Q).2.1 hpQ
      have hUnionNonempty : (C ∪ faceSetDel Q).Nonempty :=
        ⟨p0, Or.inl hp0C⟩
      have hCsubsetUnion : C ⊆ C ∪ faceSetDel Q := by
        intro p hp
        exact Or.inl hp
      have hUnionSubsetC : C ∪ faceSetDel Q ⊆ C := by
        have hmax := hComp.2.2.2 (C ∪ faceSetDel Q)
          hUnionNonempty (by simpa [Udel] using hUnionSubset)
          hUnionConnected hCsubsetUnion
        exact hmax
      intro p hpQ
      exact hUnionSubsetC (Or.inr hpQ)
    have hCsubQ : C ⊆ faceSetDel Q :=
      hCandidateMaximal Q C hCne hCsub hCconn hQsubC
    exact Set.Subset.antisymm hQsubC hCsubQ
  · intro Q' hQ'eq
    have hp0Q' : p0 ∈ faceSetDel Q' := by
      simpa [hQ'eq] using hp0C
    exact hCandidateUnique hp0Q' hp0Q
