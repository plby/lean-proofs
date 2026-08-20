import ErdosProblems.Erdos733.ST.PlaneDrawingDartSideStripsWithSectorWitnessesExist
import ErdosProblems.Erdos733.ST.PlaneDrawingDartVertexSectorGeometryExists

open Classical
noncomputable section

-- [TABLET NODE: PlaneDrawingDartLocalGeometryDataExists]
lemma PlaneDrawingDartLocalGeometryDataExists {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet] [DecidableRel G.Adj]
    (D : OrdinaryPolygonalDrawing G) (hD : D.crossingSet.card = 0)
    (A : PlaneDrawingDartArcData G D) :
    ∃ B : PlaneDrawingDartVertexStarData G D A,
      ∃ S : PlaneDrawingDartSideStripData G D A B,
        Nonempty (PlaneDrawingDartSectorWitnessData G D A B S) := by
-- BODY
  classical
  obtain ⟨C⟩ := PlaneDrawingDartVertexSectorGeometryExists G D hD A
  obtain ⟨S, hW⟩ := PlaneDrawingDartSideStripsWithSectorWitnessesExist G D hD A C
  exact ⟨C.star, S, hW⟩
