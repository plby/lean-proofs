import Util.IncidenceGeometry.CrossingFreeEdgeInteriorDisjoint
import Util.IncidenceGeometry.DartSuccessorFromLocalClockwiseNext
import Util.IncidenceGeometry.OrdinaryPolygonalDrawing
import Util.IncidenceGeometry.OrdinaryDrawingSegmentDirectionsNotSamePositiveRay
import Util.IncidenceGeometry.PlanarClockwiseSweptTwoRayEndpointConesInSector
import Util.IncidenceGeometry.PlanarSlitDiskEndpointConesAvoidRay
import Util.IncidenceGeometry.PlaneDrawingDartGeometricClockwiseSectors
import Util.IncidenceGeometry.PlaneDrawingDartArcData
import Util.IncidenceGeometry.PlaneDrawingDartFirstGermsForRadii
import Util.IncidenceGeometry.PlaneDrawingDartSourceEndpointRayCovers
import Util.IncidenceGeometry.PlaneDrawingDartUnitFirstGermsForRadii
import Util.IncidenceGeometry.PlaneDrawingDartVertexStarData
import Util.IncidenceGeometry.PlaneDrawingDartVertexSectorGeometry
import Util.IncidenceGeometry.PolygonalArc
import Util.IncidenceGeometry.PolygonalArcCarrierCompact
import Util.IncidenceGeometry.PolygonalArcReverse
import Util.IncidenceGeometry.PositiveSeparation

open Classical
noncomputable section

lemma PlaneDrawingDartVertexSectorGeometryExists {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet] [DecidableRel G.Adj]
    (D : OrdinaryPolygonalDrawing G) (hD : D.crossingSet.card = 0)
    (A : PlaneDrawingDartArcData G D) :
    Nonempty (PlaneDrawingDartVertexSectorGeometry G D A) := by
  rcases PlaneDrawingDartGeometricClockwiseSectors G D hD A with ⟨C, _hmodel⟩
  exact ⟨C⟩
