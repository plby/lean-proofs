import Util.IncidenceGeometry.PolygonalArcCompactAvoidanceScale
import Util.IncidenceGeometry.PolygonalArcSideStripAssembly
import Util.IncidenceGeometry.PolygonalArcCollarLocalSideDataExists
import Util.IncidenceGeometry.PolygonalArcCollarMiddleForbiddenMarginsExists
import Util.IncidenceGeometry.PolygonalArcCollarMiddleTubeDataExists
import Util.IncidenceGeometry.PolygonalArcCollarMiddleSegmentDataExists
import Util.IncidenceGeometry.PolygonalArcCollarControlRadiiExists

open Classical
noncomputable section

lemma PolygonalArcSideStripsAvoidCompact (γ : PolygonalArc)
    (F : Set (EuclideanSpace ℝ (Fin 2))) :
    IsCompact F →
      Disjoint F γ.carrier →
        ∃ S : PolygonalSideStrips γ, Disjoint S.collar F := by
  intro hF hFγ
  obtain ⟨η, hηpos, hηavoid⟩ := PolygonalArcCompactAvoidanceScale γ F hF hFγ
  obtain ⟨controlRadii⟩ := PolygonalArcCollarControlRadiiExists γ hηpos
  obtain ⟨middleSegments⟩ := PolygonalArcCollarMiddleSegmentDataExists γ controlRadii
  obtain ⟨forbiddenMargins⟩ :=
    PolygonalArcCollarMiddleForbiddenMarginsExists γ controlRadii middleSegments
  obtain ⟨orientedTubes, vertexLocalPieces, hlocalSideData⟩ :=
    PolygonalArcCollarLocalSideDataExists γ controlRadii middleSegments
      forbiddenMargins
  obtain ⟨localSideData⟩ := hlocalSideData
  obtain ⟨S, hS_collar, _hS_left, _hS_right, hS_eta⟩ :=
    PolygonalArcSideStripAssembly γ controlRadii middleSegments
      forbiddenMargins orientedTubes vertexLocalPieces localSideData
  refine ⟨S, ?_⟩
  rw [Set.disjoint_left]
  intro z hzS hzF
  exact hηavoid z (hS_eta z hzS) hzF
