import ErdosProblems.Erdos733.ST.DeletedEdgeDrawingImageComplementIdentity
import ErdosProblems.Erdos733.ST.PlaneFaceData

open Classical
noncomputable section

-- [TABLET NODE: DeletedEdgeCandidatePointUnique]
lemma DeletedEdgeCandidatePointUnique {V : Type*} [Fintype V]
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
    ∀ p : EuclideanSpace ℝ (Fin 2),
      p ∈ (OrdinaryDrawingImage (G.deleteEdges {e.1}) Ddel)ᶜ →
        ∃! Q : FaceDel, p ∈ faceSetDel Q := by
-- BODY
  classical
  let E := EuclideanSpace ℝ (Fin 2)
  let Udel : Set E := (OrdinaryDrawingImage (G.deleteEdges {e.1}) Ddel)ᶜ
  let Uold : Set E := (OrdinaryDrawingImage G D)ᶜ
  let rel : Set E := (D.edgeArc e).relativeInterior
  have hdeletedComplementIdentity : Udel = Uold ∪ rel := by
    dsimp [Udel, Uold, rel]
    exact DeletedEdgeDrawingImageComplementIdentity G D hD e Ddel hvertex hedges
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
        ⟨F', hF'Q', hpF'⟩ | ⟨_hnoneQ', hpRel'⟩
      · have hFF' : F = F' := hFaceUnique hpF hpF'
        subst hFF'
        exact hFQ.symm.trans hF'Q'
      · exact False.elim
          ((Set.disjoint_left.mp (hRelDisjointFace F)) hpRel' hpF)
    · rcases (hfaceSetDel Q' p).1 hpQ' with
        ⟨F', _hF'Q', hpF'⟩ | ⟨hnoneQ', _hpRel'⟩
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
  intro p hp
  rcases hCoverUdel p hp with ⟨Q, hpQ⟩
  refine ⟨Q, hpQ, ?_⟩
  intro Q' hpQ'
  exact hCandidateUnique hpQ' hpQ
