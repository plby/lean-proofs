import Mathlib.Tactic
import ErdosProblems.Erdos733.ST.PolygonalArcCollarLocalSideDataOfLocalTopologyData
import ErdosProblems.Erdos733.ST.PolygonalArcCollarLocalSideDataExists
import ErdosProblems.Erdos733.ST.PolygonalArcCollarLocalTopologyDataWithEndpointCaps
import ErdosProblems.Erdos733.ST.PolygonalArcCollarLocalTopologyDataExists
import ErdosProblems.Erdos733.ST.PolygonalArcCollarVertexLocalPieceDataExists
import ErdosProblems.Erdos733.ST.PolygonalArcEndpointDiskCappedTaperChartTransport
import ErdosProblems.Erdos733.ST.PolygonalArcInitialEndpointDiskCappedTaperSideLabelling
import ErdosProblems.Erdos733.ST.PolygonalArcInitialEndpointCone
import ErdosProblems.Erdos733.ST.PolygonalArcInteriorIncomingFrameSignedHalfTubeSectorRouting
import ErdosProblems.Erdos733.ST.PolygonalArcInteriorOutgoingFrameSignedHalfTubeSectorRouting
import ErdosProblems.Erdos733.ST.PolygonalArcInteriorTwoRaySectorChartTransport
import ErdosProblems.Erdos733.ST.PolygonalArcOpenSegmentSubsetRelativeInterior
import ErdosProblems.Erdos733.ST.PolygonalArcTerminalEndpointDiskCappedTaperSideLabelling
import ErdosProblems.Erdos733.ST.PolygonalArcTerminalEndpointCone

open Classical
noncomputable section

-- [TABLET NODE: PolygonalArcCollarLocalSideDataExistsWithEndpointCaps]
lemma PolygonalArcCollarLocalSideDataExistsWithEndpointCaps (γ : PolygonalArc)
    {η : ℝ} (controlRadii : PolygonalArcCollarControlRadii γ η)
    (middleSegments : PolygonalArcCollarMiddleSegmentData γ controlRadii)
    (forbiddenMargins :
      PolygonalArcCollarMiddleForbiddenMargins γ controlRadii middleSegments)
    (compatibleTubes :
      PolygonalArcCollarCompatibleOrientedTubeData γ controlRadii middleSegments
        forbiddenMargins)
    (r₀ r₁ K₀ K₁ : ℝ) :
    0 < r₀ →
      0 < r₁ →
        0 < K₀ →
          0 < K₁ →
            let hsource : 0 < γ.vertices.length := by
              have hlen := γ.length_ge_two
              omega
            let hfirst : 0 + 1 < γ.vertices.length := by
              have hlen := γ.length_ge_two
              omega
            let itarget : ℕ := γ.vertices.length - 1
            let htarget : itarget < γ.vertices.length := by
              have hlen := γ.length_ge_two
              dsimp [itarget]
              omega
            let jlast : ℕ := γ.vertices.length - 2
            let hlast : jlast + 1 < γ.vertices.length := by
              have hlen := γ.length_ge_two
              dsimp [jlast]
              omega
            controlRadii.radius ⟨0, hsource⟩ < r₀ →
              controlRadii.radius ⟨itarget, htarget⟩ < r₁ →
                compatibleTubes.initialConeBound 0 hfirst < K₀ →
                  compatibleTubes.terminalConeBound jlast hlast < K₁ →
                    (∀ i : Fin γ.vertices.length, i.1 ≠ 0 →
                      Disjoint
                        (Metric.ball γ.vertices[i.1] (controlRadii.radius i))
                        (Metric.ball γ.source r₀)) →
                      (∀ i : Fin γ.vertices.length, i.1 + 1 ≠ γ.vertices.length →
                        Disjoint
                          (Metric.ball γ.vertices[i.1] (controlRadii.radius i))
                          (Metric.ball γ.target r₁)) →
                    ∃ vertexLocalPieces :
                        PolygonalArcCollarVertexLocalPieceData γ controlRadii
                          middleSegments forbiddenMargins
                          compatibleTubes.orientedTubes.toPolygonalArcCollarSeparatedTubeData,
                      ∃ localSideData :
                        PolygonalArcCollarLocalSideData γ controlRadii
                          middleSegments forbiddenMargins compatibleTubes.orientedTubes
                          vertexLocalPieces,
                        γ.source ∉ localSideData.vertexCollar ⟨0, hsource⟩ ∧
                          γ.target ∉ localSideData.vertexCollar ⟨itarget, htarget⟩ ∧
                            (localSideData.vertexCollar ⟨0, hsource⟩ \
                                γ.relativeInterior ⊆
                              PolygonalArcInitialEndpointCone γ r₀ K₀) ∧
                              (localSideData.vertexCollar ⟨itarget, htarget⟩ \
                                  γ.relativeInterior ⊆
                                PolygonalArcTerminalEndpointCone γ r₁ K₁) ∧
                                (∀ i : Fin γ.vertices.length, i.1 ≠ 0 →
                                  Disjoint (localSideData.vertexCollar i)
                                    (Metric.ball γ.source r₀)) ∧
                                  (∀ i : Fin γ.vertices.length,
                                    i.1 + 1 ≠ γ.vertices.length →
                                      Disjoint (localSideData.vertexCollar i)
                                        (Metric.ball γ.target r₁)) := by
-- BODY
  intro hr₀ hr₁ hK₀ hK₁
  dsimp
  intro hρ0_lt hρT_lt hKinit_lt hKterm_lt hsourceBalls htargetBalls
  rcases PolygonalArcCollarLocalTopologyDataWithEndpointCaps γ controlRadii
      middleSegments forbiddenMargins compatibleTubes r₀ r₁ K₀ K₁
      hr₀ hr₁ hK₀ hK₁ hρ0_lt hρT_lt hKinit_lt hKterm_lt with
    ⟨vertexLocalPieces, localTopology, hsource_omit, htarget_omit,
      hsource_cone, htarget_cone, _hsource_left, _htarget_left⟩
  rcases PolygonalArcCollarLocalSideDataOfLocalTopologyData γ controlRadii
      middleSegments forbiddenMargins compatibleTubes vertexLocalPieces
      localTopology with
    ⟨localSideData, hvertexCollar_eq, _hleftSidePiece_eq, _hrightSidePiece_eq⟩
  refine
    ⟨vertexLocalPieces, localSideData, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [hvertexCollar_eq] using hsource_omit
  · simpa [hvertexCollar_eq] using htarget_omit
  · simpa [hvertexCollar_eq] using hsource_cone
  · simpa [hvertexCollar_eq] using htarget_cone
  · intro i hi
    rw [Set.disjoint_left]
    intro x hx hball
    have hxdisk : x ∈ Metric.ball γ.vertices[i.1] (controlRadii.radius i) := by
      simpa [vertexLocalPieces.vertexDisk_eq i] using
        localSideData.vertexCollar_subset_vertexDisk i hx
    exact (Set.disjoint_left.mp (hsourceBalls i hi))
      hxdisk hball
  · intro i hi
    rw [Set.disjoint_left]
    intro x hx hball
    have hxdisk : x ∈ Metric.ball γ.vertices[i.1] (controlRadii.radius i) := by
      simpa [vertexLocalPieces.vertexDisk_eq i] using
        localSideData.vertexCollar_subset_vertexDisk i hx
    exact (Set.disjoint_left.mp (htargetBalls i hi))
      hxdisk hball
