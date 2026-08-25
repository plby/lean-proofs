import Util.IncidenceGeometry.ComplementComponent
import Util.IncidenceGeometry.DrawingFaceComponent
import Util.IncidenceGeometry.OrdinaryDrawingImage
import Util.IncidenceGeometry.OrdinaryPolygonalDrawing
import Util.IncidenceGeometry.PlaneDrawingDartArcDataExists
import Util.IncidenceGeometry.PlaneDrawingDartLocalGeometryDataExists
import Util.IncidenceGeometry.PlaneDrawingDartSectorData
import Util.IncidenceGeometry.PolygonalArc
import Util.IncidenceGeometry.PolygonalArcSideStripAssembly
import Util.IncidenceGeometry.PolygonalSideStrips
import Util.IncidenceGeometry.PositiveSeparation

open Classical
noncomputable section

lemma PlaneDrawingDartSectorCompatibility {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet] [DecidableRel G.Adj]
    (D : OrdinaryPolygonalDrawing G) (hD : D.crossingSet.card = 0) :
    Nonempty (PlaneDrawingDartSectorData G D) := by
  rcases PlaneDrawingDartArcDataExists G D hD with ⟨A⟩
  rcases PlaneDrawingDartLocalGeometryDataExists G D hD A with ⟨B, S, ⟨W⟩⟩
  exact ⟨{
    dartEdge := A.dartEdge
    dartEdge_eq := A.dartEdge_eq
    dartArc := A.dartArc
    dartArc_carrier := A.dartArc_carrier
    dartArc_source := A.dartArc_source
    dartArc_target := A.dartArc_target
    leftSideStrip := S.leftSideStrip
    rightSideStrip := S.rightSideStrip
    sideStripData := S.sideStripData
    rightSideStrip_eq_leftSideStrip_symm := S.rightSideStrip_eq_leftSideStrip_symm
    localComplement_subset_sideStrips := S.localComplement_subset_sideStrips
    leftSide_unique_face_component := S.leftSide_unique_face_component
    rightSide_unique_face_component := S.rightSide_unique_face_component
    localDiskRadius := B.localDiskRadius
    localDiskRadius_pos := B.localDiskRadius_pos
    germDirection := B.germDirection
    germDirection_ne_zero := B.germDirection_ne_zero
    radialGerm := B.radialGerm
    radialGerm_eq_openSegment := B.radialGerm_eq_openSegment
    radialGerm_subset_dartArc := B.radialGerm_subset_dartArc
    localDisk_meets_drawing_only_incident_germs :=
      B.localDisk_meets_drawing_only_incident_germs
    clockwiseNext := B.clockwiseNext
    fullClockwiseTurn := B.fullClockwiseTurn
    fullClockwiseTurn_pos := B.fullClockwiseTurn_pos
    clockwiseTurn := B.clockwiseTurn
    clockwiseTurn_pos := B.clockwiseTurn_pos
    clockwiseTurn_le_full := B.clockwiseTurn_le_full
    clockwiseTurn_full_iff_same := B.clockwiseTurn_full_iff_same
    clockwiseNext_first_after := B.clockwiseNext_first_after
    clockwiseNext_eq_self_iff_isolated := B.clockwiseNext_eq_self_iff_isolated
    successor := B.successor
    successor_tail := B.successor_tail
    successor_eq_clockwiseNext := B.successor_eq_clockwiseNext
    successor_single_incident := B.successor_single_incident
    successor_clockwise_sector := W.successor_clockwise_sector
    vertex_sector_coverage := W.vertex_sector_coverage
  }⟩
