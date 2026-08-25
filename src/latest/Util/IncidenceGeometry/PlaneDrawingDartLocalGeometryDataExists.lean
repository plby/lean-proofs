import Util.IncidenceGeometry.PlaneDrawingDartSideStripsWithSectorWitnessesExist
import Util.IncidenceGeometry.PlaneDrawingDartVertexSectorGeometryExists

open Classical
noncomputable section

lemma PlaneDrawingDartLocalGeometryDataExists {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet] [DecidableRel G.Adj]
    (D : OrdinaryPolygonalDrawing G) (hD : D.crossingSet.card = 0)
    (A : PlaneDrawingDartArcData G D) :
    ∃ B : PlaneDrawingDartVertexStarData G D A,
      ∃ S : PlaneDrawingDartSideStripData G D A B,
        Nonempty (PlaneDrawingDartSectorWitnessData G D A B S) := by
  classical
  obtain ⟨C⟩ := PlaneDrawingDartVertexSectorGeometryExists G D hD A
  obtain ⟨S, hW⟩ := PlaneDrawingDartSideStripsWithSectorWitnessesExist G D hD A C
  exact ⟨C.star, S, hW⟩
