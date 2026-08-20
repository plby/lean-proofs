import ErdosProblems.Erdos733.ST.PlaneFaceData
import ErdosProblems.Erdos733.ST.DrawingFaceComponent
import ErdosProblems.Erdos733.ST.ComplementComponent
import ErdosProblems.Erdos733.ST.FiniteAuxiliaryFaceQuotient
import ErdosProblems.Erdos733.ST.OrdinaryDrawingImage
import ErdosProblems.Erdos733.ST.DeletedEdgeDrawingImageComplementIdentity
import ErdosProblems.Erdos733.ST.OrdinaryDrawingImageCompact
import ErdosProblems.Erdos733.ST.OrdinaryPolygonalDrawing
import ErdosProblems.Erdos733.ST.PolygonalArc
import ErdosProblems.Erdos733.ST.PolygonalArcCollar
import ErdosProblems.Erdos733.ST.PolygonalSideStrips
import ErdosProblems.Erdos733.ST.DeletedEdgeLocalIncidentFaces
import ErdosProblems.Erdos733.ST.OpenConnectedComponentPolygonallyConnected
import ErdosProblems.Erdos733.ST.FinitePolygonalPerturbation
import ErdosProblems.Erdos733.ST.DeletedEdgeCandidateFaceSetBasic
import ErdosProblems.Erdos733.ST.DeletedEdgeCandidateFaceSetMaximal
import ErdosProblems.Erdos733.ST.DeletedEdgeCandidateFacesComplete
import ErdosProblems.Erdos733.ST.DeletedEdgeCandidatePointUnique
import Mathlib.Combinatorics.SimpleGraph.Acyclic

open Classical
noncomputable section

-- [TABLET NODE: DeletedEdgeComplementComponents]
lemma DeletedEdgeComplementComponents {V : Type*} [Fintype V] (G : SimpleGraph V)
    [Fintype G.edgeSet] [DecidableRel G.Adj] (D : OrdinaryPolygonalDrawing G)
    (hD : D.crossingSet.card = 0) (A : PlaneFaceData G D) (e : G.edgeFinset)
    (Ddel : OrdinaryPolygonalDrawing (G.deleteEdges {e.1}))
    (hvertex : Ddel.vertexPlacement = D.vertexPlacement)
    (hedges :
      ∀ ed : (G.deleteEdges {e.1}).edgeFinset,
        ∃ eG : G.edgeFinset, eG.1 = ed.1 ∧ eG.1 ≠ e.1 ∧
          Ddel.edgeArc ed = D.edgeArc eG)
    (d : G.Dart) (hd : d.edge = e.1) :
    let sideAtom : Option A.Face → Prop :=
      fun x => x = none ∨ x = some (A.leftFace d) ∨ x = some (A.leftFace d.symm)
    ∃ (FaceDel : Type*) (_faceDelFintype : Fintype FaceDel)
        (faceSetDel : FaceDel → Set (EuclideanSpace ℝ (Fin 2)))
        (componentOf : Option A.Face → FaceDel),
      (OrdinaryDrawingImage (G.deleteEdges {e.1}) Ddel)ᶜ =
          (OrdinaryDrawingImage G D)ᶜ ∪ (D.edgeArc e).relativeInterior ∧
        Function.Surjective componentOf ∧
          (∀ x y : Option A.Face,
            componentOf x = componentOf y ↔ x = y ∨ (sideAtom x ∧ sideAtom y)) ∧
            (∀ (Q : FaceDel) (p : EuclideanSpace ℝ (Fin 2)),
              p ∈ faceSetDel Q ↔
                (∃ F : A.Face, componentOf (some F) = Q ∧ p ∈ A.faceSet F) ∨
                  (componentOf none = Q ∧ p ∈ (D.edgeArc e).relativeInterior)) ∧
              (∀ Q : FaceDel,
                DrawingFaceComponent (G.deleteEdges {e.1}) Ddel (faceSetDel Q)) ∧
                (∀ C : Set (EuclideanSpace ℝ (Fin 2)),
                  DrawingFaceComponent (G.deleteEdges {e.1}) Ddel C →
                    ∃! Q : FaceDel, faceSetDel Q = C) ∧
                  ∀ p : EuclideanSpace ℝ (Fin 2),
                    p ∈ (OrdinaryDrawingImage (G.deleteEdges {e.1}) Ddel)ᶜ →
                      ∃! Q : FaceDel, p ∈ faceSetDel Q := by
-- BODY
  letI : Fintype A.Face := A.faceFintype
  rcases FiniteAuxiliaryFaceQuotient A.Face (A.leftFace d) (A.leftFace d.symm) with
    ⟨FaceDel, faceDelFintype, componentOf, hcomponent_surj, hcomponent_eq⟩
  let faceSetDel : FaceDel → Set (EuclideanSpace ℝ (Fin 2)) :=
    fun Q =>
      {p |
        (∃ F : A.Face, componentOf (some F) = Q ∧ p ∈ A.faceSet F) ∨
          (componentOf none = Q ∧ p ∈ (D.edgeArc e).relativeInterior)}
  have hfaceSetDel :
      ∀ (Q : FaceDel) (p : EuclideanSpace ℝ (Fin 2)),
        p ∈ faceSetDel Q ↔
          (∃ F : A.Face, componentOf (some F) = Q ∧ p ∈ A.faceSet F) ∨
            (componentOf none = Q ∧ p ∈ (D.edgeArc e).relativeInterior) := by
    intro Q p
    rfl
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
  have hOldSubset :
      ∀ F : A.Face, A.faceSet F ⊆ (OrdinaryDrawingImage G D)ᶜ := fun F =>
    (hOldComponent F).2.1
  have hOldConnected : ∀ F : A.Face, IsConnected (A.faceSet F) := fun F =>
    (hOldComponent F).2.2.1
  have hleftAttachmentSubsetDel :
      A.faceSet (A.leftFace d) ∪ (D.edgeArc e).relativeInterior ⊆
        (OrdinaryDrawingImage (G.deleteEdges {e.1}) Ddel)ᶜ := by
    intro x hx
    rw [hdeletedComplementIdentity]
    rcases hx with hxFace | hxRel
    · exact Or.inl (hOldSubset (A.leftFace d) hxFace)
    · exact Or.inr hxRel
  have hrightAttachmentSubsetDel :
      A.faceSet (A.leftFace d.symm) ∪ (D.edgeArc e).relativeInterior ⊆
        (OrdinaryDrawingImage (G.deleteEdges {e.1}) Ddel)ᶜ := by
    intro x hx
    rw [hdeletedComplementIdentity]
    rcases hx with hxFace | hxRel
    · exact Or.inl (hOldSubset (A.leftFace d.symm) hxFace)
    · exact Or.inr hxRel
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
  refine ⟨FaceDel, faceDelFintype, faceSetDel, componentOf, ?_, ?_⟩
  · exact hdeletedComplementIdentity
  refine ⟨hcomponent_surj, ?_⟩
  refine ⟨?_, ?_⟩
  · intro x y
    simpa using hcomponent_eq x y
  refine ⟨?_, ?_⟩
  · intro Q p
    exact hfaceSetDel Q p
  refine ⟨?_, ?_⟩
  · intro Q
    change ComplementComponent (OrdinaryDrawingImage (G.deleteEdges {e.1}) Ddel)
      (faceSetDel Q)
    have hbasicQ :=
      DeletedEdgeCandidateFaceSetBasic G D hD A e Ddel hvertex hedges d hd
        FaceDel faceDelFintype componentOf hcomponent_surj hcomponent_eq
        faceSetDel hfaceSetDel Q
    refine ⟨hbasicQ.1, hbasicQ.2.1, hbasicQ.2.2, ?_⟩
    intro C hCne hCsub hCconn hQC
    exact
      DeletedEdgeCandidateFaceSetMaximal G D hD A e Ddel hvertex hedges d hd
        FaceDel faceDelFintype componentOf hcomponent_surj hcomponent_eq
        faceSetDel hfaceSetDel Q C hCne hCsub hCconn hQC
  refine ⟨?_, ?_⟩
  · exact
      DeletedEdgeCandidateFacesComplete G D hD A e Ddel hvertex hedges d hd
        FaceDel faceDelFintype componentOf hcomponent_surj hcomponent_eq
        faceSetDel hfaceSetDel
  exact
    DeletedEdgeCandidatePointUnique G D hD A e Ddel hvertex hedges d hd
      FaceDel faceDelFintype componentOf hcomponent_surj hcomponent_eq
      faceSetDel hfaceSetDel
