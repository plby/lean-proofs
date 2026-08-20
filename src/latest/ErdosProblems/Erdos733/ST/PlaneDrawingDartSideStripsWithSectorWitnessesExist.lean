import ErdosProblems.Erdos733.ST.ConnectedSubsetContainedInUniqueComplementComponent
import ErdosProblems.Erdos733.ST.DrawingFaceComponent
import ErdosProblems.Erdos733.ST.OrdinaryDrawingImageWithoutEdge
import ErdosProblems.Erdos733.ST.PlaneDrawingDartCollarChoiceData
import ErdosProblems.Erdos733.ST.PlaneDrawingDartCollarChoiceDataExists
import ErdosProblems.Erdos733.ST.PlaneDrawingDartSectorWitnessDataFromCollarChoices
import ErdosProblems.Erdos733.ST.PlaneDrawingDartArcData
import ErdosProblems.Erdos733.ST.PlaneDrawingDartSectorWitnessData
import ErdosProblems.Erdos733.ST.PlaneDrawingDartSideStripData
import ErdosProblems.Erdos733.ST.PlaneDrawingDartSideStripDataFromCollarChoices
import ErdosProblems.Erdos733.ST.PlaneDrawingDartVertexStarData
import ErdosProblems.Erdos733.ST.PlaneDrawingDartVertexSectorGeometry
import ErdosProblems.Erdos733.ST.PlaneDrawingSelectedEdgeAwayFromEndpointCompact
import ErdosProblems.Erdos733.ST.PolygonalArc
import ErdosProblems.Erdos733.ST.PolygonalArcCarrierCompact
import ErdosProblems.Erdos733.ST.PolygonalArcCollarCompatibleOrientedTubeDataExistsBelow
import ErdosProblems.Erdos733.ST.PolygonalArcCollarControlRadiiExistsBelow
import ErdosProblems.Erdos733.ST.PolygonalArcCollarLocalSideData
import ErdosProblems.Erdos733.ST.PolygonalArcCollarLocalSideDataExistsWithEndpointLeftCones
import ErdosProblems.Erdos733.ST.PolygonalArcCollarMiddleForbiddenMarginsExists
import ErdosProblems.Erdos733.ST.PolygonalArcCollarMiddleSegmentDataExists
import ErdosProblems.Erdos733.ST.PolygonalArcCollarVertexLocalPieceData
import ErdosProblems.Erdos733.ST.PolygonalArcEndpointIsolationExists
import ErdosProblems.Erdos733.ST.PolygonalArcInitialEndpointDiskCappedTaperAttachmentStrengthening
import ErdosProblems.Erdos733.ST.PolygonalArcInitialEndpointLeftCone
import ErdosProblems.Erdos733.ST.PolygonalArcOpenSegmentSubsetRelativeInterior
import ErdosProblems.Erdos733.ST.PolygonalArcTerminalEndpointDiskCappedTaperAttachmentStrengthening
import ErdosProblems.Erdos733.ST.PolygonalArcSideStripAssembly
import ErdosProblems.Erdos733.ST.PolygonalArcTerminalEndpointLeftCone
import ErdosProblems.Erdos733.ST.PolygonalSideStrips
import ErdosProblems.Erdos733.ST.PositiveSeparation

open Classical
noncomputable section

-- [TABLET NODE: PlaneDrawingDartSideStripsWithSectorWitnessesExist]
lemma PlaneDrawingDartSideStripsWithSectorWitnessesExist {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet] [DecidableRel G.Adj]
    (D : OrdinaryPolygonalDrawing G) (hD : D.crossingSet.card = 0)
    (A : PlaneDrawingDartArcData G D)
    (C : PlaneDrawingDartVertexSectorGeometry G D A) :
    ∃ S : PlaneDrawingDartSideStripData G D A C.star,
      Nonempty (PlaneDrawingDartSectorWitnessData G D A C.star S) := by
-- BODY
  obtain ⟨P⟩ := PlaneDrawingDartCollarChoiceDataExists G D hD A C
  obtain ⟨S, hleft, _hright⟩ :=
    PlaneDrawingDartSideStripDataFromCollarChoices G D A C P
  exact ⟨S, PlaneDrawingDartSectorWitnessDataFromCollarChoices G D A C P S hleft⟩
