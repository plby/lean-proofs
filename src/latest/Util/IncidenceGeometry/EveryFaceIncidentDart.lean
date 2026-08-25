import Util.IncidenceGeometry.ComplementComponent
import Util.IncidenceGeometry.ComplementComponentNearestPointContactApproach
import Util.IncidenceGeometry.ConnectedGraphVertexIncidentDart
import Util.IncidenceGeometry.DrawingFaceComponent
import Util.IncidenceGeometry.OrdinaryDrawingImageContactDichotomy
import Util.IncidenceGeometry.OrdinaryDrawingImage
import Util.IncidenceGeometry.OrdinaryDrawingImageCompact
import Util.IncidenceGeometry.OrdinaryPolygonalDrawing
import Util.IncidenceGeometry.PlaneFaceDataEdgeInteriorLocalSideIncidentFace
import Util.IncidenceGeometry.PlaneFaceDataVertexSectorIncidentFace
import Util.IncidenceGeometry.PlaneFaceData
import Util.IncidenceGeometry.PolygonalArc
import Util.IncidenceGeometry.PolygonalSideStrips
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

open Classical
noncomputable section

lemma EveryFaceIncidentDart {V : Type*} [Fintype V] (G : SimpleGraph V)
    [Fintype G.edgeSet] [DecidableRel G.Adj] (D : OrdinaryPolygonalDrawing G)
    (hD : D.crossingSet.card = 0) (A : PlaneFaceData G D) :
    G.Connected → 3 ≤ Fintype.card V → 0 < G.edgeFinset.card →
      ∀ F : A.Face, ∃ d : G.Dart, A.leftFace d = F := by
  intro hconn hn hedge F
  have _hDcrossing : D.crossingSet.card = 0 := hD
  have hFaceComponent :
      ComplementComponent (OrdinaryDrawingImage G D) (A.faceSet F) := by
    simpa [DrawingFaceComponent] using A.face_component F
  have hFaceComponentData := hFaceComponent
  rcases hFaceComponentData with
    ⟨hFaceNonempty, hFaceSubsetCompl, _hFaceConnected, _hFaceMax⟩
  rcases hFaceNonempty with ⟨p, hpF⟩
  have hpComplement : p ∈ (OrdinaryDrawingImage G D)ᶜ :=
    hFaceSubsetCompl hpF
  have hVertexIncident : ∀ v : V, ∃ d : G.Dart, d.toProd.2 = v :=
    ConnectedGraphVertexIncidentDart G hconn hedge
  have hVertexSectorIncident :
      ∀ (v : V) (y : EuclideanSpace ℝ (Fin 2)),
        y ∈ A.faceSet F →
          y ∈ Metric.ball (D.vertexPlacement v) (A.localDiskRadius v) →
            y ≠ D.vertexPlacement v →
              y ∈ (OrdinaryDrawingImage G D)ᶜ →
                ∃ d : G.Dart, A.leftFace d = F := by
    intro v y hyF hyBall hyNe hyCompl
    exact PlaneFaceDataVertexSectorIncidentFace G D A F v y hyF
      (hVertexIncident v) hyBall hyNe hyCompl
  have hEdgeInteriorIncident :
      ∀ (d : G.Dart) (x : EuclideanSpace ℝ (Fin 2)),
        x ∈ (A.dartArc d).relativeInterior →
          ∃ U : Set (EuclideanSpace ℝ (Fin 2)),
            IsOpen U ∧ x ∈ U ∧
              ∀ y : EuclideanSpace ℝ (Fin 2),
                y ∈ A.faceSet F →
                  y ∈ U →
                    y ∈ (OrdinaryDrawingImage G D)ᶜ →
                      ∃ a : G.Dart, A.leftFace a = F :=
    PlaneFaceDataEdgeInteriorLocalSideIncidentFace G D A F
  have hImageNonempty : (OrdinaryDrawingImage G D).Nonempty := by
    have hcard_pos : 0 < Fintype.card V :=
      lt_of_lt_of_le (by norm_num : (0 : ℕ) < 3) hn
    rcases Fintype.card_pos_iff.mp hcard_pos with ⟨v⟩
    refine ⟨D.vertexPlacement v, ?_⟩
    rw [OrdinaryDrawingImage]
    exact Or.inl ⟨v, rfl⟩
  rcases (OrdinaryDrawingImageCompact G D).exists_infDist_eq_dist hImageNonempty p with
    ⟨x, hxImage, hnearest⟩
  have hApproach :
      ∀ U : Set (EuclideanSpace ℝ (Fin 2)),
        IsOpen U → x ∈ U →
          ∃ y, y ∈ A.faceSet F ∧ y ∈ U ∧
            y ∈ (OrdinaryDrawingImage G D)ᶜ ∧ y ≠ x :=
    ComplementComponentNearestPointContactApproach
      (OrdinaryDrawingImage G D) (A.faceSet F) p x
      hFaceComponent hpF hxImage hnearest
  rcases OrdinaryDrawingImageContactDichotomy G D A x hxImage with
    ⟨v, hxVertex⟩ | ⟨d, hxRel⟩
  · have hxBall :
        x ∈ Metric.ball (D.vertexPlacement v) (A.localDiskRadius v) := by
      rw [hxVertex]
      exact Metric.mem_ball_self (A.localDiskRadius_pos v)
    rcases hApproach
        (Metric.ball (D.vertexPlacement v) (A.localDiskRadius v))
        Metric.isOpen_ball hxBall with
      ⟨y, hyF, hyBall, hyCompl, hyNeX⟩
    have hyNeVertex : y ≠ D.vertexPlacement v := by
      intro hyEq
      exact hyNeX (hyEq.trans hxVertex.symm)
    exact hVertexSectorIncident v y hyF hyBall hyNeVertex hyCompl
  · rcases hEdgeInteriorIncident d x hxRel with
      ⟨U, hUopen, hxU, hUincident⟩
    rcases hApproach U hUopen hxU with
      ⟨y, hyF, hyU, hyCompl, _hyNeX⟩
    exact hUincident y hyF hyU hyCompl
