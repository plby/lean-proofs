import ErdosProblems.Erdos733.ST.PlaneFaceData
import ErdosProblems.Erdos733.ST.OrdinaryDrawingImage
import ErdosProblems.Erdos733.ST.OrdinaryPolygonalDrawing
import ErdosProblems.Erdos733.ST.PolygonalPath
import ErdosProblems.Erdos733.ST.DeletedEdgeDrawingImageComplementIdentity
import ErdosProblems.Erdos733.ST.DeletedEdgeLocalIncidentFaces
import ErdosProblems.Erdos733.ST.FinitePolygonalPerturbation
import ErdosProblems.Erdos733.ST.OrdinaryDrawingImageCompact
import ErdosProblems.Erdos733.ST.PolygonalPathCarrierConnected

open Classical
noncomputable section

-- [TABLET NODE: DeletedEdgePathAtomClassification]
lemma DeletedEdgePathAtomClassification {V : Type*} [Fintype V]
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
    (componentOf : Option A.Face → FaceDel)
    (hcomponent_eq :
      ∀ x y : Option A.Face,
        componentOf x = componentOf y ↔
          x = y ∨
            ((x = none ∨ x = some (A.leftFace d) ∨
                x = some (A.leftFace d.symm)) ∧
              (y = none ∨ y = some (A.leftFace d) ∨
                y = some (A.leftFace d.symm))))
    (γ : PolygonalPath) (x y : Option A.Face)
    (hx :
      γ.source ∈
        (match x with
        | none => (D.edgeArc e).relativeInterior
        | some F => A.faceSet F))
    (hy :
      γ.target ∈
        (match y with
        | none => (D.edgeArc e).relativeInterior
        | some F => A.faceSet F))
    (hγ :
      γ.carrier ⊆ (OrdinaryDrawingImage (G.deleteEdges {e.1}) Ddel)ᶜ) :
    componentOf x = componentOf y := by
-- BODY
  classical
  let E := EuclideanSpace ℝ (Fin 2)
  let Udel : Set E := (OrdinaryDrawingImage (G.deleteEdges {e.1}) Ddel)ᶜ
  let Uold : Set E := (OrdinaryDrawingImage G D)ᶜ
  let rel : Set E := (D.edgeArc e).relativeInterior
  let sideAtom : Option A.Face → Prop :=
    fun z => z = none ∨ z = some (A.leftFace d) ∨ z = some (A.leftFace d.symm)
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
  have hOldConnected : ∀ F : A.Face, IsConnected (A.faceSet F) := by
    intro F
    exact (hOldComponent F).2.2.1
  have hOldMaximal :
      ∀ F : A.Face, ∀ C : Set E,
        C.Nonempty → C ⊆ Uold → IsConnected C → A.faceSet F ⊆ C →
          C ⊆ A.faceSet F := by
    intro F
    exact (hOldComponent F).2.2.2
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
  have hFaceDisjoint :
      ∀ {F F' : A.Face}, F ≠ F' → Disjoint (A.faceSet F) (A.faceSet F') := by
    intro F F' hne
    rw [Set.disjoint_left]
    intro p hpF hpF'
    exact hne (hFaceUnique hpF hpF')
  have hUoldOpen : IsOpen Uold := by
    dsimp [Uold]
    exact (OrdinaryDrawingImageCompact G D).isClosed.isOpen_compl
  have hFaceOpen : ∀ F : A.Face, IsOpen (A.faceSet F) := by
    intro F
    rw [Metric.isOpen_iff]
    intro p hpF
    have hpOld : p ∈ Uold := hOldSubset F hpF
    rcases Metric.isOpen_iff.mp hUoldOpen p hpOld with ⟨r, hrpos, hballOld⟩
    refine ⟨r, hrpos, ?_⟩
    intro z hz
    have hpBall : p ∈ Metric.ball p r := by
      simpa using hrpos
    have hsegBall : segment ℝ p z ⊆ Metric.ball p r := by
      intro q hq
      exact (convex_ball p r).segment_subset hpBall hz hq
    have hsegOld : segment ℝ p z ⊆ Uold := by
      intro q hq
      exact hballOld (hsegBall hq)
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
  have hUdelOpen : IsOpen Udel := by
    dsimp [Udel]
    exact
      (OrdinaryDrawingImageCompact (G.deleteEdges {e.1}) Ddel).isClosed.isOpen_compl
  have hNonSideComplementOpen :
      ∀ F : A.Face, ¬ sideAtom (some F) → IsOpen (Udel \ A.faceSet F) := by
    intro F hFnonSide
    rw [isOpen_iff_forall_mem_open]
    intro p hp
    rcases hp with ⟨hpUdel, hpNotF⟩
    have hpCases : p ∈ Uold ∪ rel := by
      simpa [hdeletedComplementIdentity] using hpUdel
    rcases hpCases with hpOld | hpRel
    · rcases A.complement_point_face p hpOld with ⟨F0, hpF0, _huniq⟩
      have hF0_ne_F : F0 ≠ F := by
        intro hF0eq
        exact hpNotF (by simpa [hF0eq] using hpF0)
      refine ⟨A.faceSet F0, ?_, hFaceOpen F0, hpF0⟩
      intro q hqF0
      refine ⟨?_, ?_⟩
      · rw [hdeletedComplementIdentity]
        exact Or.inl (hOldSubset F0 hqF0)
      · intro hqF
        exact hF0_ne_F (hFaceUnique hqF0 hqF)
    · rcases DeletedEdgeLocalIncidentFaces G D hD A e d hd p hpRel with
        ⟨N, hNopen, hpN, hNsubset⟩
      refine ⟨N ∩ Udel, ?_, hNopen.inter hUdelOpen, ⟨hpN, hpUdel⟩⟩
      intro q hq
      rcases hq with ⟨hqN, hqUdel⟩
      refine ⟨hqUdel, ?_⟩
      intro hqF
      have hqOld : q ∈ Uold := hOldSubset F hqF
      have hqSide :
          q ∈ A.faceSet (A.leftFace d) ∪ A.faceSet (A.leftFace d.symm) :=
        hNsubset ⟨hqN, hqOld⟩
      rcases hqSide with hqLeft | hqRight
      · have hFleft : F = A.leftFace d := hFaceUnique hqF hqLeft
        exact hFnonSide (Or.inr (Or.inl (by simp [hFleft])))
      · have hFright : F = A.leftFace d.symm := hFaceUnique hqF hqRight
        exact hFnonSide (Or.inr (Or.inr (by simp [hFright])))
  have hsourceCarrier : γ.source ∈ γ.carrier := by
    rw [γ.carrier_eq]
    left
    exact Or.inl rfl
  have htargetCarrier : γ.target ∈ γ.carrier := by
    rw [γ.carrier_eq]
    left
    exact Or.inr rfl
  have hCarrierConnected : IsConnected γ.carrier :=
    PolygonalPathCarrierConnected γ
  have hCarrierSubsetNonSideFace :
      ∀ F : A.Face, ¬ sideAtom (some F) →
        (∃ p : E, p ∈ γ.carrier ∧ p ∈ A.faceSet F) →
          γ.carrier ⊆ A.faceSet F := by
    intro F hFnonSide hmeet q hqCarrier
    by_contra hqNotF
    have hcover : γ.carrier ⊆ A.faceSet F ∪ (Udel \ A.faceSet F) := by
      intro z hz
      by_cases hzF : z ∈ A.faceSet F
      · exact Or.inl hzF
      · exact Or.inr ⟨hγ hz, hzF⟩
    have hFmeet : (γ.carrier ∩ A.faceSet F).Nonempty := by
      rcases hmeet with ⟨p, hpCarrier, hpF⟩
      exact ⟨p, hpCarrier, hpF⟩
    have hNotFmeet : (γ.carrier ∩ (Udel \ A.faceSet F)).Nonempty :=
      ⟨q, hqCarrier, hγ hqCarrier, hqNotF⟩
    have hinter :
        (γ.carrier ∩ (A.faceSet F ∩ (Udel \ A.faceSet F))).Nonempty :=
      hCarrierConnected.isPreconnected (A.faceSet F) (Udel \ A.faceSet F)
        (hFaceOpen F) (hNonSideComplementOpen F hFnonSide) hcover
        hFmeet hNotFmeet
    rcases hinter with ⟨z, _hzCarrier, hzF, hzNotF⟩
    exact hzNotF.2 hzF
  have hSameAtomFromNonSideSource :
      ∀ F : A.Face, ¬ sideAtom (some F) → γ.source ∈ A.faceSet F →
        y = some F := by
    intro F hFnonSide hsourceF
    have hsub : γ.carrier ⊆ A.faceSet F :=
      hCarrierSubsetNonSideFace F hFnonSide
        ⟨γ.source, hsourceCarrier, hsourceF⟩
    have htargetF : γ.target ∈ A.faceSet F := hsub htargetCarrier
    cases y with
    | none =>
        exact False.elim
          ((Set.disjoint_left.mp (hRelDisjointFace F)) (by simpa [rel] using hy) htargetF)
    | some F' =>
        have hF'F : F' = F := hFaceUnique hy htargetF
        simp [hF'F]
  have hSameAtomFromNonSideTarget :
      ∀ F : A.Face, ¬ sideAtom (some F) → γ.target ∈ A.faceSet F →
        x = some F := by
    intro F hFnonSide htargetF
    have hsub : γ.carrier ⊆ A.faceSet F :=
      hCarrierSubsetNonSideFace F hFnonSide
        ⟨γ.target, htargetCarrier, htargetF⟩
    have hsourceF : γ.source ∈ A.faceSet F := hsub hsourceCarrier
    cases x with
    | none =>
        exact False.elim
          ((Set.disjoint_left.mp (hRelDisjointFace F)) (by simpa [rel] using hx) hsourceF)
    | some F' =>
        have hF'F : F' = F := hFaceUnique hx hsourceF
        simp [hF'F]
  by_cases hxSide : sideAtom x
  · by_cases hySide : sideAtom y
    · exact (hcomponent_eq x y).2 (Or.inr ⟨hxSide, hySide⟩)
    · cases y with
      | none =>
          exact False.elim (hySide (Or.inl rfl))
      | some Fy =>
          have hxEq : x = some Fy :=
            hSameAtomFromNonSideTarget Fy hySide hy
          exact (hcomponent_eq x (some Fy)).2 (Or.inl hxEq)
  · cases x with
    | none =>
        exact False.elim (hxSide (Or.inl rfl))
    | some Fx =>
        have hyEq : y = some Fx :=
          hSameAtomFromNonSideSource Fx hxSide hx
        exact (hcomponent_eq (some Fx) y).2 (Or.inl hyEq.symm)
