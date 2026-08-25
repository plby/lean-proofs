import Util.IncidenceGeometry.ConnectedSubsetContainedInUniqueComplementComponent
import Util.IncidenceGeometry.DrawingFaceComponent
import Util.IncidenceGeometry.OrdinaryDrawingImageWithoutEdge
import Util.IncidenceGeometry.PlaneDrawingDartCollarChoiceData
import Util.IncidenceGeometry.PlaneDrawingDartCollarChoiceDataExists
import Util.IncidenceGeometry.PlaneDrawingDartSectorWitnessDataFromCollarChoices
import Util.IncidenceGeometry.PlaneDrawingDartArcData
import Util.IncidenceGeometry.PlaneDrawingDartSectorWitnessData
import Util.IncidenceGeometry.PlaneDrawingDartSideStripData
import Util.IncidenceGeometry.PlaneDrawingDartSideStripDataFromCollarChoices
import Util.IncidenceGeometry.PlaneDrawingDartVertexStarData
import Util.IncidenceGeometry.PlaneDrawingDartVertexSectorGeometry
import Util.IncidenceGeometry.PlaneDrawingSelectedEdgeAwayFromEndpointCompact
import Util.IncidenceGeometry.PolygonalArc
import Util.IncidenceGeometry.PolygonalArcCarrierCompact
import Util.IncidenceGeometry.PolygonalArcCollarCompatibleOrientedTubeDataExistsBelow
import Util.IncidenceGeometry.PolygonalArcCollarControlRadiiExistsBelow
import Util.IncidenceGeometry.PolygonalArcCollarLocalSideData
import Util.IncidenceGeometry.PolygonalArcCollarLocalSideDataExistsWithEndpointLeftCones
import Util.IncidenceGeometry.PolygonalArcCollarMiddleForbiddenMarginsExists
import Util.IncidenceGeometry.PolygonalArcCollarMiddleSegmentDataExists
import Util.IncidenceGeometry.PolygonalArcCollarVertexLocalPieceData
import Util.IncidenceGeometry.PolygonalArcEndpointIsolationExists
import Util.IncidenceGeometry.PolygonalArcInitialEndpointDiskCappedTaperAttachmentStrengthening
import Util.IncidenceGeometry.PolygonalArcInitialEndpointLeftCone
import Util.IncidenceGeometry.PolygonalArcOpenSegmentSubsetRelativeInterior
import Util.IncidenceGeometry.PolygonalArcTerminalEndpointDiskCappedTaperAttachmentStrengthening
import Util.IncidenceGeometry.PolygonalArcSideStripAssembly
import Util.IncidenceGeometry.PolygonalArcTerminalEndpointLeftCone
import Util.IncidenceGeometry.PolygonalSideStrips
import Util.IncidenceGeometry.PositiveSeparation

open Classical
noncomputable section

lemma PlaneDrawingDartSideStripsWithSectorWitnessesExist {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet] [DecidableRel G.Adj]
    (D : OrdinaryPolygonalDrawing G) (hD : D.crossingSet.card = 0)
    (A : PlaneDrawingDartArcData G D)
    (C : PlaneDrawingDartVertexSectorGeometry G D A) :
    ∃ S : PlaneDrawingDartSideStripData G D A C.star,
      Nonempty (PlaneDrawingDartSectorWitnessData G D A C.star S) := by
  obtain ⟨P⟩ := PlaneDrawingDartCollarChoiceDataExists G D hD A C
  obtain ⟨S, hleft, _hright⟩ :=
    PlaneDrawingDartSideStripDataFromCollarChoices G D A C P
  exact ⟨S, PlaneDrawingDartSectorWitnessDataFromCollarChoices G D A C P S hleft⟩
