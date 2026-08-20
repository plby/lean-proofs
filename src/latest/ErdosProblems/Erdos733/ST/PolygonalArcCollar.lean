import ErdosProblems.Erdos733.ST.OrdinaryPolygonalDrawing
import ErdosProblems.Erdos733.ST.PolygonalArc
import ErdosProblems.Erdos733.ST.PolygonalSideStrips
import ErdosProblems.Erdos733.ST.DrawingFaceComponent
import ErdosProblems.Erdos733.ST.ComplementComponent
import ErdosProblems.Erdos733.ST.OrdinaryDrawingImage
import ErdosProblems.Erdos733.ST.PositiveSeparation
import ErdosProblems.Erdos733.ST.PolygonalArcSideStripsAvoidCompact
import ErdosProblems.Erdos733.ST.PlaneDrawingEdgeArcSideStripsAvoidImage
import ErdosProblems.Erdos733.ST.ConnectedSubsetContainedInUniqueComplementComponent

open Classical
noncomputable section

-- [TABLET NODE: PolygonalArcCollar]
lemma PolygonalArcCollar (γ : PolygonalArc)
    (F : Set (EuclideanSpace ℝ (Fin 2))) :
    IsCompact F →
      Disjoint F γ.carrier →
        (∃ S : PolygonalSideStrips γ, Disjoint S.collar F) ∧
          ∀ {V : Type*} [Fintype V] (G : SimpleGraph V)
            [Fintype G.edgeSet] [DecidableRel G.Adj]
            (D : OrdinaryPolygonalDrawing G) (hD : D.crossingSet.card = 0)
            (e : G.edgeFinset),
            D.edgeArc e = γ →
              ∃ S : PolygonalSideStrips γ,
                Disjoint S.collar F ∧
                  (∃! L : Set (EuclideanSpace ℝ (Fin 2)),
                    DrawingFaceComponent G D L ∧ S.leftStrip ⊆ L) ∧
                  (∃! R : Set (EuclideanSpace ℝ (Fin 2)),
                    DrawingFaceComponent G D R ∧ S.rightStrip ⊆ R) := by
-- BODY
  intro hF hFγ
  constructor
  · exact PolygonalArcSideStripsAvoidCompact γ F hF hFγ
  · intro V _ G _ _ D hD e hγ
    obtain ⟨S, hSF, hS_image, hLeft, hRight⟩ :=
      PlaneDrawingEdgeArcSideStripsAvoidImage G D hD e γ F hF hFγ hγ
    refine ⟨S, hSF, ?_, ?_⟩
    · simpa [DrawingFaceComponent] using
        ConnectedSubsetContainedInUniqueComplementComponent
          (OrdinaryDrawingImage G D) S.leftStrip S.left_connected.1 hLeft S.left_connected
    · simpa [DrawingFaceComponent] using
        ConnectedSubsetContainedInUniqueComplementComponent
          (OrdinaryDrawingImage G D) S.rightStrip S.right_connected.1 hRight S.right_connected
