import ErdosProblems.Erdos733.ST.ConnectedSubsetContainedInUniqueComplementComponent
import ErdosProblems.Erdos733.ST.DrawingFaceComponent
import ErdosProblems.Erdos733.ST.OrdinaryDrawingImage
import ErdosProblems.Erdos733.ST.OrdinaryDrawingImageWithoutEdge
import ErdosProblems.Erdos733.ST.PlaneDrawingDartArcData
import ErdosProblems.Erdos733.ST.PlaneDrawingDartCollarChoiceData
import ErdosProblems.Erdos733.ST.PlaneDrawingDartSideStripData
import ErdosProblems.Erdos733.ST.PlaneDrawingDartVertexStarData
import ErdosProblems.Erdos733.ST.PlaneDrawingDartVertexSectorGeometry
import ErdosProblems.Erdos733.ST.PolygonalArc
import ErdosProblems.Erdos733.ST.PolygonalArcCollarLocalSideData
import ErdosProblems.Erdos733.ST.PolygonalArcInitialEndpointDiskCappedTaperAttachmentStrengthening
import ErdosProblems.Erdos733.ST.PolygonalArcInitialEndpointLeftCone
import ErdosProblems.Erdos733.ST.PolygonalArcOpenSegmentSubsetRelativeInterior
import ErdosProblems.Erdos733.ST.PolygonalArcTerminalEndpointDiskCappedTaperAttachmentStrengthening
import ErdosProblems.Erdos733.ST.PolygonalArcTerminalEndpointLeftCone
import ErdosProblems.Erdos733.ST.PolygonalSideStrips
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

open Classical
noncomputable section

-- [TABLET NODE: PlaneDrawingDartSideStripDataFromCollarChoices]
lemma PlaneDrawingDartSideStripDataFromCollarChoices {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet] [DecidableRel G.Adj]
    (D : OrdinaryPolygonalDrawing G) (A : PlaneDrawingDartArcData G D)
    (C : PlaneDrawingDartVertexSectorGeometry G D A)
    (P : PlaneDrawingDartCollarChoiceData G D A C) :
    ∃ S : PlaneDrawingDartSideStripData G D A C.star,
      (∀ d : G.Dart, S.leftSideStrip d = (P.sideStrips d).leftStrip) ∧
        (∀ d : G.Dart, S.rightSideStrip d = (P.sideStrips d).rightStrip) := by
-- BODY
  refine ⟨?_, ?_, ?_⟩
  · refine
      { leftSideStrip := fun d => (P.sideStrips d).leftStrip
        rightSideStrip := fun d => (P.sideStrips d).rightStrip
        sideStripData := ?_
        rightSideStrip_eq_leftSideStrip_symm := ?_
        leftSideStrip_subset_complement := ?_
        rightSideStrip_subset_complement := ?_
        localComplement_subset_sideStrips := ?_
        leftSide_unique_face_component := ?_
        rightSide_unique_face_component := ?_ }
    · intro d
      exact ⟨P.sideStrips d, rfl, rfl⟩
    · intro d
      exact P.rightStrip_eq_leftStrip_symm d
    · intro d
      exact P.leftStrip_subset_complement d
    · intro d x hx
      have hxleft : x ∈ (P.sideStrips d.symm).leftStrip := by
        simpa [P.rightStrip_eq_leftStrip_symm d] using hx
      exact P.leftStrip_subset_complement d.symm hxleft
    · intro d x hx
      exact P.localComplement_subset_sideStrips d x hx
    · intro d
      simpa [DrawingFaceComponent] using
        (ConnectedSubsetContainedInUniqueComplementComponent
          (OrdinaryDrawingImage G D) (P.sideStrips d).leftStrip
          (P.leftStrip_nonempty d) (P.leftStrip_subset_complement d)
          (P.sideStrips d).left_connected)
    · intro d
      have hright_nonempty : ((P.sideStrips d).rightStrip).Nonempty := by
        simpa [P.rightStrip_eq_leftStrip_symm d] using P.leftStrip_nonempty d.symm
      have hright_subset :
          (P.sideStrips d).rightStrip ⊆ (OrdinaryDrawingImage G D)ᶜ := by
        intro x hx
        have hxleft : x ∈ (P.sideStrips d.symm).leftStrip := by
          simpa [P.rightStrip_eq_leftStrip_symm d] using hx
        exact P.leftStrip_subset_complement d.symm hxleft
      simpa [DrawingFaceComponent] using
        (ConnectedSubsetContainedInUniqueComplementComponent
          (OrdinaryDrawingImage G D) (P.sideStrips d).rightStrip
          hright_nonempty hright_subset (P.sideStrips d).right_connected)
  · intro d
    rfl
  · intro d
    rfl
