import Util.IncidenceGeometry.ComplementComponent
import Util.IncidenceGeometry.DrawingFaceComponent
import Util.IncidenceGeometry.PlaneFaceData
import Util.IncidenceGeometry.PolygonalSideStrips
import Util.IncidenceGeometry.PolygonalJordanSeparation
import Util.IncidenceGeometry.OpenConnectedComponentPolygonallyConnected
import Util.IncidenceGeometry.OrdinaryDrawingImageCompact
import Util.IncidenceGeometry.PlaneFaceDataJordanCurveSideStripsSeparated
import Util.IncidenceGeometry.DeleteNonbridgeSimpleClosedCurveWitness
import Util.IncidenceGeometry.ComplementComponentAbsorbsConnectedSubset
import Util.IncidenceGeometry.PolygonalPathCarrierConnected
import Mathlib.Combinatorics.SimpleGraph.Acyclic

open Classical
noncomputable section

lemma DeleteNonbridgeSideFacesDistinct {V : Type*} [Fintype V] (G : SimpleGraph V)
    [Fintype G.edgeSet] [DecidableRel G.Adj] (D : OrdinaryPolygonalDrawing G)
    (hD : D.crossingSet.card = 0) (A : PlaneFaceData G D) (e : G.edgeFinset)
    (hconn : G.Connected) (he : ¬ G.IsBridge e.1) :
    ∃ d : G.Dart, d.edge = e.1 ∧ A.leftFace d ≠ A.leftFace d.symm := by
  classical
  rcases DeleteNonbridgeSimpleClosedCurveWitness G D hD A e hconn he with
    ⟨d, hd, J, hJsubset, hedge⟩
  rcases PlaneFaceDataJordanCurveSideStripsSeparated G D A J d hJsubset hedge with
    ⟨Cleft, Cright, hCleft, hCright, hCneq, hLeftNonempty, hRightNonempty,
      hLeftSubset, hRightSubset⟩
  refine ⟨d, hd, ?_⟩
  intro hfaces
  rcases hLeftNonempty with ⟨p, hpLeft⟩
  rcases hRightNonempty with ⟨q, hqRight⟩
  have hpFace : p ∈ A.faceSet (A.leftFace d) :=
    A.leftFace_contains d hpLeft
  have hqFaceSymm : q ∈ A.faceSet (A.leftFace d.symm) :=
    A.leftFace_contains d.symm hqRight
  have hqFace : q ∈ A.faceSet (A.leftFace d) := by
    simpa [hfaces] using hqFaceSymm
  have hFaceComp :
      ComplementComponent (OrdinaryDrawingImage G D) (A.faceSet (A.leftFace d)) := by
    simpa [DrawingFaceComponent] using A.face_component (A.leftFace d)
  have hImageComplOpen : IsOpen (OrdinaryDrawingImage G D)ᶜ :=
    (OrdinaryDrawingImageCompact G D).isClosed.isOpen_compl
  have hPathConn :
      PolygonallyPathConnected (A.faceSet (A.leftFace d)) := by
    exact OpenConnectedComponentPolygonallyConnected (OrdinaryDrawingImage G D)ᶜ
      (A.faceSet (A.leftFace d)) hImageComplOpen (by
        simpa [compl_compl] using hFaceComp)
  rcases hPathConn hpFace hqFace with ⟨η, hηsource, hηtarget, hηcarrier⟩
  have hηNonempty : η.carrier.Nonempty := by
    refine ⟨p, ?_⟩
    have hpCarrier : η.source ∈ η.carrier := by
      rw [η.carrier_eq]
      exact Or.inl (Or.inl rfl)
    simpa [hηsource] using hpCarrier
  have hηConn : IsConnected η.carrier := PolygonalPathCarrierConnected η
  have hηJcompl : η.carrier ⊆ J.carrierᶜ := by
    intro x hxη hxJ
    have hxFace : x ∈ A.faceSet (A.leftFace d) := hηcarrier hxη
    have hxImageCompl : x ∈ (OrdinaryDrawingImage G D)ᶜ := hFaceComp.2.1 hxFace
    exact hxImageCompl (hJsubset hxJ)
  have hηMeetLeft : (Cleft ∩ η.carrier).Nonempty := by
    refine ⟨p, hLeftSubset hpLeft, ?_⟩
    have hpCarrier : η.source ∈ η.carrier := by
      rw [η.carrier_eq]
      exact Or.inl (Or.inl rfl)
    simpa [hηsource] using hpCarrier
  have hηSubsetLeft : η.carrier ⊆ Cleft :=
    ComplementComponentAbsorbsConnectedSubset J.carrier Cleft η.carrier
      hCleft hηNonempty hηJcompl hηConn hηMeetLeft
  have hqCarrier : q ∈ η.carrier := by
    have htargetCarrier : η.target ∈ η.carrier := by
      rw [η.carrier_eq]
      exact Or.inl (Or.inr rfl)
    simpa [hηtarget] using htargetCarrier
  have hqLeft : q ∈ Cleft := hηSubsetLeft hqCarrier
  have hqCright : q ∈ Cright := hRightSubset hqRight
  have hRightSubsetLeft : Cright ⊆ Cleft :=
    ComplementComponentAbsorbsConnectedSubset J.carrier Cleft Cright
      hCleft hCright.1 hCright.2.1 hCright.2.2.1
      ⟨q, hqLeft, hqCright⟩
  have hLeftSubsetRight : Cleft ⊆ Cright :=
    ComplementComponentAbsorbsConnectedSubset J.carrier Cright Cleft
      hCright hCleft.1 hCleft.2.1 hCleft.2.2.1
      ⟨q, hqCright, hqLeft⟩
  exact hCneq (Set.Subset.antisymm hLeftSubsetRight hRightSubsetLeft)
