import Util.IncidenceGeometry.ComplementComponentAbsorbsConnectedSubset
import Util.IncidenceGeometry.PlaneFaceData

open Classical
noncomputable section

lemma PlaneFaceDataVertexSectorIncidentFace {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet] [DecidableRel G.Adj]
    (D : OrdinaryPolygonalDrawing G) (A : PlaneFaceData G D) :
    ∀ (F : A.Face) (v : V) (y : EuclideanSpace ℝ (Fin 2)),
      y ∈ A.faceSet F →
        (∃ d : G.Dart, d.toProd.2 = v) →
          y ∈ Metric.ball (D.vertexPlacement v) (A.localDiskRadius v) →
            y ≠ D.vertexPlacement v →
              y ∈ (OrdinaryDrawingImage G D)ᶜ →
                ∃ d : G.Dart, A.leftFace d = F := by
  intro F v y hyF hvIncident hyBall hyNe hyCompl
  rcases A.vertex_sector_coverage v y hvIncident hyBall hyNe hyCompl with
    ⟨d, _hdHead, sector, hySector, _hsectorOpen, hsectorConnected,
      _hsectorBall, hsectorCompl, hsectorLeft, _hsectorSuccLeft,
      _hsectorDisjoint⟩
  have hFaceComponent :
      ComplementComponent (OrdinaryDrawingImage G D) (A.faceSet F) := by
    simpa [DrawingFaceComponent] using A.face_component F
  have hsectorNonempty : sector.Nonempty := ⟨y, hySector⟩
  have hsectorMeet : (A.faceSet F ∩ sector).Nonempty := ⟨y, hyF, hySector⟩
  have hsectorSubsetFace : sector ⊆ A.faceSet F :=
    ComplementComponentAbsorbsConnectedSubset
      (OrdinaryDrawingImage G D) (A.faceSet F) sector hFaceComponent
      hsectorNonempty hsectorCompl hsectorConnected hsectorMeet
  rcases hsectorLeft with ⟨z, ⟨⟨hzSector, hzLeft⟩, _hzBall⟩⟩
  have hzF : z ∈ A.faceSet F := hsectorSubsetFace hzSector
  have hzLeftFace : z ∈ A.faceSet (A.leftFace d) :=
    A.leftFace_contains d hzLeft
  have hzCompl : z ∈ (OrdinaryDrawingImage G D)ᶜ :=
    hsectorCompl hzSector
  rcases A.complement_point_face z hzCompl with ⟨F0, _hzF0, huniq⟩
  have hleft : A.leftFace d = F0 := huniq (A.leftFace d) hzLeftFace
  have hF : F = F0 := huniq F hzF
  exact ⟨d, hleft.trans hF.symm⟩
