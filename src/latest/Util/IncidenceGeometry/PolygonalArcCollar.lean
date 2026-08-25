import Util.IncidenceGeometry.OrdinaryPolygonalDrawing
import Util.IncidenceGeometry.PolygonalArc
import Util.IncidenceGeometry.PolygonalSideStrips
import Util.IncidenceGeometry.DrawingFaceComponent
import Util.IncidenceGeometry.ComplementComponent
import Util.IncidenceGeometry.OrdinaryDrawingImage
import Util.IncidenceGeometry.PositiveSeparation
import Util.IncidenceGeometry.PolygonalArcSideStripsAvoidCompact
import Util.IncidenceGeometry.PlaneDrawingEdgeArcSideStripsAvoidImage
import Util.IncidenceGeometry.ConnectedSubsetContainedInUniqueComplementComponent

open Classical
noncomputable section

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
