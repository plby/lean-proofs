import Util.IncidenceGeometry.DeleteEdgeOldFaceMap
import Util.IncidenceGeometry.DeletedEdgeComplementComponents
import Util.IncidenceGeometry.DeletedEdgeDrawingImageComplementIdentity
import Util.IncidenceGeometry.DeletedEdgeLocalIncidentFaces
import Util.IncidenceGeometry.FinitePolygonalPerturbation
import Util.IncidenceGeometry.OpenConnectedComponentPolygonallyConnected
import Util.IncidenceGeometry.OrdinaryDrawingImageCompact
import Util.IncidenceGeometry.PlaneFaceData
import Util.IncidenceGeometry.TwoPointFiberSurjectiveCard

open Classical
noncomputable section

lemma DeleteEdgeOldFaceMapTwoFaceQuotient {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet] [DecidableRel G.Adj]
    (D : OrdinaryPolygonalDrawing G) (hD : D.crossingSet.card = 0)
    (A : PlaneFaceData G D) (e : G.edgeFinset)
    (Ddel : OrdinaryPolygonalDrawing (G.deleteEdges {e.1}))
    (Adel : PlaneFaceData (G.deleteEdges {e.1}) Ddel)
    (hvertex : Ddel.vertexPlacement = D.vertexPlacement)
    (hedges :
      ∀ ed : (G.deleteEdges {e.1}).edgeFinset,
        ∃ eG : G.edgeFinset, eG.1 = ed.1 ∧ eG.1 ≠ e.1 ∧
          Ddel.edgeArc ed = D.edgeArc eG)
    (d : G.Dart) (hd : d.edge = e.1)
    (hside : A.leftFace d ≠ A.leftFace d.symm) :
    ∃ oldToNew : A.Face → Adel.Face,
      (∀ F : A.Face, A.faceSet F ⊆ Adel.faceSet (oldToNew F)) ∧
        oldToNew (A.leftFace d) = oldToNew (A.leftFace d.symm) ∧
          (D.edgeArc e).relativeInterior ⊆
            Adel.faceSet (oldToNew (A.leftFace d)) ∧
            (∀ F F' : A.Face,
              oldToNew F = oldToNew F' ↔
                F = F' ∨
                  (F = A.leftFace d ∧ F' = A.leftFace d.symm) ∨
                    (F = A.leftFace d.symm ∧ F' = A.leftFace d)) ∧
              (∀ F : A.Face,
                F ≠ A.leftFace d → F ≠ A.leftFace d.symm →
                  Adel.faceSet (oldToNew F) = A.faceSet F) ∧
                (∀ Fdel : Adel.Face, ∃ F : A.Face, oldToNew F = Fdel) ∧
                  @Fintype.card Adel.Face Adel.faceFintype + 1 =
                    @Fintype.card A.Face A.faceFintype := by
  classical
  letI : Fintype A.Face := A.faceFintype
  letI : Fintype Adel.Face := Adel.faceFintype
  rcases
    (DeletedEdgeComplementComponents.{_, 0, _} G D hD A e Ddel hvertex hedges d hd)
    with
    ⟨FaceDel, faceDelFintype, faceSetDel, componentOf, _hcomplement,
      hcomponent_surj, hcomponent_eq, hfaceSetDel, hface_component,
      hfaces_complete, _hpoint_unique⟩
  let toAdel : FaceDel → Adel.Face := fun Q =>
    Classical.choose
      (ExistsUnique.exists (Adel.faces_complete (faceSetDel Q) (hface_component Q)))
  have htoAdel_spec :
      ∀ Q : FaceDel, Adel.faceSet (toAdel Q) = faceSetDel Q := by
    intro Q
    exact
      Classical.choose_spec
        (ExistsUnique.exists (Adel.faces_complete (faceSetDel Q) (hface_component Q)))
  have htoAdel_eq_of_faceSet :
      ∀ {Q : FaceDel} {Fdel : Adel.Face},
        faceSetDel Q = Adel.faceSet Fdel → toAdel Q = Fdel := by
    intro Q Fdel hQ
    exact
      ExistsUnique.unique (Adel.faces_complete (faceSetDel Q) (hface_component Q))
        (htoAdel_spec Q) hQ.symm
  let oldToNew : A.Face → Adel.Face := fun F => toAdel (componentOf (some F))
  have hsideComponentEq := by
    exact
      (hcomponent_eq (some (A.leftFace d)) (some (A.leftFace d.symm))).2
        (Or.inr ⟨Or.inr (Or.inl rfl), Or.inr (Or.inr rfl)⟩)
  have hnoneComponentEq := by
    exact
      (hcomponent_eq none (some (A.leftFace d))).2
        (Or.inr ⟨Or.inl rfl, Or.inr (Or.inl rfl)⟩)
  have hmerge : oldToNew (A.leftFace d) = oldToNew (A.leftFace d.symm) := by
    change toAdel (componentOf (some (A.leftFace d))) =
      toAdel (componentOf (some (A.leftFace d.symm)))
    exact congrArg toAdel hsideComponentEq
  have hcontains : ∀ F : A.Face, A.faceSet F ⊆ Adel.faceSet (oldToNew F) := by
    intro F x hx
    change x ∈ Adel.faceSet (toAdel (componentOf (some F)))
    rw [htoAdel_spec]
    exact (hfaceSetDel (componentOf (some F)) x).2 (Or.inl ⟨F, rfl, hx⟩)
  have hrelint :
      (D.edgeArc e).relativeInterior ⊆
        Adel.faceSet (oldToNew (A.leftFace d)) := by
    intro x hx
    change x ∈ Adel.faceSet (toAdel (componentOf (some (A.leftFace d))))
    rw [htoAdel_spec]
    exact (hfaceSetDel (componentOf (some (A.leftFace d))) x).2
      (Or.inr ⟨hnoneComponentEq, hx⟩)
  have hfiber :
      ∀ F F' : A.Face,
        oldToNew F = oldToNew F' ↔
          F = F' ∨
            (F = A.leftFace d ∧ F' = A.leftFace d.symm) ∨
              (F = A.leftFace d.symm ∧ F' = A.leftFace d) := by
    intro F F'
    constructor
    · intro hFF'
      have hset :
          faceSetDel (componentOf (some F)) =
            faceSetDel (componentOf (some F')) := by
        calc
          faceSetDel (componentOf (some F)) =
              Adel.faceSet (toAdel (componentOf (some F))) := (htoAdel_spec _).symm
          _ = Adel.faceSet (toAdel (componentOf (some F'))) := by
            change Adel.faceSet (oldToNew F) = Adel.faceSet (oldToNew F')
            rw [hFF']
          _ = faceSetDel (componentOf (some F')) := htoAdel_spec _
      have hQeq := by
        exact
          ExistsUnique.unique
            (hfaces_complete (faceSetDel (componentOf (some F'))) (hface_component _))
            hset rfl
      have hrel := (hcomponent_eq (some F) (some F')).1 hQeq
      rcases hrel with hsome | hsideBoth
      · exact Or.inl (Option.some.inj hsome)
      · rcases hsideBoth with ⟨hFside, hF'side⟩
        rcases hFside with hnone | hFL | hFR
        · cases hnone
        · have hF_FL : F = A.leftFace d := Option.some.inj hFL
          rcases hF'side with hnone' | hFL' | hFR'
          · cases hnone'
          · have hF'_FL : F' = A.leftFace d := Option.some.inj hFL'
            exact Or.inl (hF_FL.trans hF'_FL.symm)
          · have hF'_FR : F' = A.leftFace d.symm := Option.some.inj hFR'
            exact Or.inr (Or.inl ⟨hF_FL, hF'_FR⟩)
        · have hF_FR : F = A.leftFace d.symm := Option.some.inj hFR
          rcases hF'side with hnone' | hFL' | hFR'
          · cases hnone'
          · have hF'_FL : F' = A.leftFace d := Option.some.inj hFL'
            exact Or.inr (Or.inr ⟨hF_FR, hF'_FL⟩)
          · have hF'_FR : F' = A.leftFace d.symm := Option.some.inj hFR'
            exact Or.inl (hF_FR.trans hF'_FR.symm)
    · intro hrel
      rcases hrel with hEq | hcross | hcross
      · cases hEq
        rfl
      · rcases hcross with ⟨hF, hF'⟩
        cases hF
        cases hF'
        exact hmerge
      · rcases hcross with ⟨hF, hF'⟩
        cases hF
        cases hF'
        exact hmerge.symm
  have hunchanged :
      ∀ F : A.Face,
        F ≠ A.leftFace d → F ≠ A.leftFace d.symm →
          Adel.faceSet (oldToNew F) = A.faceSet F := by
    intro F hFleft hFright
    ext x
    change x ∈ Adel.faceSet (toAdel (componentOf (some F))) ↔ x ∈ A.faceSet F
    rw [htoAdel_spec, hfaceSetDel]
    constructor
    · intro hx
      rcases hx with hOld | hRel
      · rcases hOld with ⟨F', hcomp, hxF'⟩
        have hrel := (hcomponent_eq (some F') (some F)).1 hcomp
        rcases hrel with hsome | hsideBoth
        · have hFprimeF : F' = F := Option.some.inj hsome
          simpa [hFprimeF] using hxF'
        · rcases hsideBoth with ⟨_hF'side, hFside⟩
          rcases hFside with hnone | hFL | hFR
          · cases hnone
          · exact False.elim (hFleft (Option.some.inj hFL))
          · exact False.elim (hFright (Option.some.inj hFR))
      · rcases hRel with ⟨hnone, _hxrel⟩
        have hrel := (hcomponent_eq none (some F)).1 hnone
        rcases hrel with hnoneSome | hsideBoth
        · cases hnoneSome
        · rcases hsideBoth with ⟨_hnoneSide, hFside⟩
          rcases hFside with hnone' | hFL | hFR
          · cases hnone'
          · exact False.elim (hFleft (Option.some.inj hFL))
          · exact False.elim (hFright (Option.some.inj hFR))
    · intro hx
      exact Or.inl ⟨F, rfl, hx⟩
  have hsurjOld : ∀ Fdel : Adel.Face, ∃ F : A.Face, oldToNew F = Fdel := by
    intro Fdel
    have hFdelComp :
        DrawingFaceComponent (G.deleteEdges {e.1}) Ddel (Adel.faceSet Fdel) := by
      simpa [DrawingFaceComponent] using Adel.face_component Fdel
    rcases hfaces_complete (Adel.faceSet Fdel) hFdelComp with
      ⟨Q, hQset, _hQuniq⟩
    rcases hcomponent_surj Q with ⟨atom, hatom⟩
    cases atom with
    | none =>
        refine ⟨A.leftFace d, ?_⟩
        change toAdel (componentOf (some (A.leftFace d))) = Fdel
        have hQeq :=
          hnoneComponentEq.symm.trans hatom
        rw [hQeq]
        exact htoAdel_eq_of_faceSet hQset
    | some F =>
        refine ⟨F, ?_⟩
        change toAdel (componentOf (some F)) = Fdel
        rw [hatom]
        exact htoAdel_eq_of_faceSet hQset
  have hcard :
      @Fintype.card Adel.Face Adel.faceFintype + 1 =
        @Fintype.card A.Face A.faceFintype := by
    exact
      TwoPointFiberSurjectiveCard (A.leftFace d) (A.leftFace d.symm) hside
        oldToNew hsurjOld hfiber
  exact ⟨oldToNew, hcontains, hmerge, hrelint, hfiber, hunchanged, hsurjOld, hcard⟩
