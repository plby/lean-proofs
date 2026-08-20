import ErdosProblems.Erdos733.ST.CrossingFreeEdgeInteriorDisjoint
import ErdosProblems.Erdos733.ST.DartSuccessorFromLocalClockwiseNext
import ErdosProblems.Erdos733.ST.OrdinaryPolygonalDrawing
import ErdosProblems.Erdos733.ST.OrdinaryDrawingSegmentDirectionsNotSamePositiveRay
import ErdosProblems.Erdos733.ST.PlanarClockwiseSweptTwoRayEndpointConesInSector
import ErdosProblems.Erdos733.ST.PlanarSlitDiskEndpointConesAvoidRay
import ErdosProblems.Erdos733.ST.PlaneDrawingDartGeometricClockwiseSectors
import ErdosProblems.Erdos733.ST.PlaneDrawingDartArcData
import ErdosProblems.Erdos733.ST.PlaneDrawingDartFirstGermsForRadii
import ErdosProblems.Erdos733.ST.PlaneDrawingDartSourceEndpointRayCovers
import ErdosProblems.Erdos733.ST.PlaneDrawingDartUnitFirstGermsForRadii
import ErdosProblems.Erdos733.ST.PlaneDrawingDartVertexStarData
import ErdosProblems.Erdos733.ST.PlaneDrawingDartVertexSectorGeometry
import ErdosProblems.Erdos733.ST.PolygonalArc
import ErdosProblems.Erdos733.ST.PolygonalArcCarrierCompact
import ErdosProblems.Erdos733.ST.PolygonalArcReverse
import ErdosProblems.Erdos733.ST.PositiveSeparation

open Classical
noncomputable section

-- [TABLET NODE: PlaneDrawingDartVertexSectorGeometryExists]
lemma PlaneDrawingDartVertexSectorGeometryExists {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet] [DecidableRel G.Adj]
    (D : OrdinaryPolygonalDrawing G) (hD : D.crossingSet.card = 0)
    (A : PlaneDrawingDartArcData G D) :
    Nonempty (PlaneDrawingDartVertexSectorGeometry G D A) := by
-- BODY
  rcases PlaneDrawingDartGeometricClockwiseSectors G D hD A with ⟨C, _hmodel⟩
  exact ⟨C⟩
