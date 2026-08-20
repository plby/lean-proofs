import Mathlib.Tactic
import ErdosProblems.Erdos733.ST.PolygonalArcCollarCompatibleOrientedTubeDataExistsBelow
import ErdosProblems.Erdos733.ST.PolygonalArcCollarControlRadiiExistsBelow
import ErdosProblems.Erdos733.ST.PolygonalArcCollarLocalSideDataOfLocalTopologyData
import ErdosProblems.Erdos733.ST.PolygonalArcCollarLocalTopologyDataWithEndpointCaps
import ErdosProblems.Erdos733.ST.PolygonalArcCollarMiddleForbiddenMarginsExists
import ErdosProblems.Erdos733.ST.PolygonalArcCollarMiddleSegmentDataExists
import ErdosProblems.Erdos733.ST.PolygonalArcSideStripAssembly

open Classical
noncomputable section

-- [TABLET NODE: OrdinaryAdjacentEdgesConcreteCollarGeometry]
lemma OrdinaryAdjacentEdgesConcreteCollarGeometry (Aarc : PolygonalArc)
    (eta r0 r1 K0 K1 : ℝ)
    (heta : 0 < eta)
    (hIso : PolygonalArcEndpointIsolation Aarc r0 r1)
    (hK0 : 0 < K0) (hK1 : 0 < K1) :
    ∃ controlRadii : PolygonalArcCollarControlRadii Aarc eta,
      ∃ middleSegments : PolygonalArcCollarMiddleSegmentData Aarc controlRadii,
        ∃ forbiddenMargins : PolygonalArcCollarMiddleForbiddenMargins
            Aarc controlRadii middleSegments,
          ∃ compatibleTubes : PolygonalArcCollarCompatibleOrientedTubeData
              Aarc controlRadii middleSegments forbiddenMargins,
            ∃ vertexLocalPieces : PolygonalArcCollarVertexLocalPieceData Aarc
                controlRadii middleSegments forbiddenMargins
                compatibleTubes.orientedTubes.toPolygonalArcCollarSeparatedTubeData,
              ∃ localSideData : PolygonalArcCollarLocalSideData Aarc controlRadii
                  middleSegments forbiddenMargins compatibleTubes.orientedTubes
                  vertexLocalPieces,
                ∃ S : PolygonalSideStrips Aarc,
                  (let hsource : 0 < Aarc.vertices.length := by
                      have hlen := Aarc.length_ge_two
                      omega
                   let hfirst : 0 + 1 < Aarc.vertices.length := by
                      have hlen := Aarc.length_ge_two
                      omega
                   let itarget : ℕ := Aarc.vertices.length - 1
                   let htarget : itarget < Aarc.vertices.length := by
                      have hlen := Aarc.length_ge_two
                      dsimp [itarget]
                      omega
                   let jlast : ℕ := Aarc.vertices.length - 2
                   let hlast : jlast + 1 < Aarc.vertices.length := by
                      have hlen := Aarc.length_ge_two
                      dsimp [jlast]
                      omega
                   controlRadii.radius ⟨0, hsource⟩ < r0 ∧
                     controlRadii.radius ⟨itarget, htarget⟩ < r1 ∧
                     compatibleTubes.initialConeBound 0 hfirst < K0 ∧
                     compatibleTubes.terminalConeBound jlast hlast < K1 ∧
                     (∀ i : Fin Aarc.vertices.length, i.1 ≠ 0 →
                       Disjoint
                         (Metric.ball Aarc.vertices[i.1] (controlRadii.radius i))
                         (Metric.ball Aarc.source r0)) ∧
                     (∀ i : Fin Aarc.vertices.length,
                       i.1 + 1 ≠ Aarc.vertices.length →
                         Disjoint
                           (Metric.ball Aarc.vertices[i.1] (controlRadii.radius i))
                           (Metric.ball Aarc.target r1)) ∧
                     Aarc.source ∉ localSideData.vertexCollar ⟨0, hsource⟩ ∧
                     Aarc.target ∉ localSideData.vertexCollar ⟨itarget, htarget⟩ ∧
                     (localSideData.vertexCollar ⟨0, hsource⟩ \
                         Aarc.relativeInterior ⊆
                       PolygonalArcInitialEndpointCone Aarc r0 K0) ∧
                     (localSideData.vertexCollar ⟨itarget, htarget⟩ \
                         Aarc.relativeInterior ⊆
                       PolygonalArcTerminalEndpointCone Aarc r1 K1) ∧
                     S.collar =
                       ((⋃ (j : ℕ), ⋃ (hj : j + 1 < Aarc.vertices.length),
                           compatibleTubes.orientedTubes.toPolygonalArcCollarSeparatedTubeData.tube
                             j hj) ∪
                         (⋃ i : Fin Aarc.vertices.length,
                           localSideData.vertexCollar i)) ∧
                     S.leftStrip =
                       ((⋃ (j : ℕ), ⋃ (hj : j + 1 < Aarc.vertices.length),
                           compatibleTubes.orientedTubes.toPolygonalArcCollarSeparatedTubeData.leftHalf
                             j hj) ∪
                         (⋃ i : Fin Aarc.vertices.length,
                           localSideData.leftSidePiece i)) ∧
                     S.rightStrip =
                       ((⋃ (j : ℕ), ⋃ (hj : j + 1 < Aarc.vertices.length),
                           compatibleTubes.orientedTubes.toPolygonalArcCollarSeparatedTubeData.rightHalf
                             j hj) ∪
                         (⋃ i : Fin Aarc.vertices.length,
                           localSideData.rightSidePiece i)) ∧
                     (∀ z ∈ S.collar, ∃ p ∈ Aarc.carrier, dist z p < eta) ∧
                     (let E := EuclideanSpace ℝ (Fin 2)
                      let d0 : E := Aarc.vertices[1] - Aarc.vertices[0]
                      let chart0 : E → E := fun z =>
                        Aarc.vertices[0] + z 0 • d0 + z 1 • PlanarRot90 d0
                      let a0 : ℝ :=
                        controlRadii.radius ⟨0, hsource⟩ /
                          dist Aarc.vertices[0] Aarc.vertices[1]
                      let kappa0 : ℝ :=
                        compatibleTubes.initialConeBound 0 hfirst
                      let C0 : Set E :=
                        {z | 0 < z 0 ∧ z 0 ^ 2 + z 1 ^ 2 < a0 ^ 2 ∧
                          -kappa0 * z 0 < z 1 ∧ z 1 < kappa0 * z 0}
                      let L0 : Set E :=
                        {z | 0 < z 0 ∧ z 0 ^ 2 + z 1 ^ 2 < a0 ^ 2 ∧
                          0 < z 1 ∧ z 1 < kappa0 * z 0}
                      let R0 : Set E :=
                        {z | 0 < z 0 ∧ z 0 ^ 2 + z 1 ^ 2 < a0 ^ 2 ∧
                          -kappa0 * z 0 < z 1 ∧ z 1 < 0}
                      let dT : E :=
                        Aarc.vertices[jlast] - Aarc.vertices[itarget]
                      let chartT : E → E := fun z =>
                        Aarc.vertices[itarget] + z 0 • dT +
                          z 1 • PlanarRot90 dT
                      let aT : ℝ :=
                        controlRadii.radius ⟨itarget, htarget⟩ /
                          dist Aarc.vertices[itarget] Aarc.vertices[jlast]
                      let kappaT : ℝ :=
                        compatibleTubes.terminalConeBound jlast hlast
                      let CT : Set E :=
                        {z | 0 < z 0 ∧ z 0 ^ 2 + z 1 ^ 2 < aT ^ 2 ∧
                          -kappaT * z 0 < z 1 ∧ z 1 < kappaT * z 0}
                      let LT : Set E :=
                        {z | 0 < z 0 ∧ z 0 ^ 2 + z 1 ^ 2 < aT ^ 2 ∧
                          0 < z 1 ∧ z 1 < kappaT * z 0}
                      let RT : Set E :=
                        {z | 0 < z 0 ∧ z 0 ^ 2 + z 1 ^ 2 < aT ^ 2 ∧
                          -kappaT * z 0 < z 1 ∧ z 1 < 0}
                      localSideData.vertexCollar ⟨0, hsource⟩ = chart0 '' C0 ∧
                        localSideData.leftSidePiece ⟨0, hsource⟩ = chart0 '' L0 ∧
                        localSideData.rightSidePiece ⟨0, hsource⟩ = chart0 '' R0 ∧
                        localSideData.vertexCollar ⟨itarget, htarget⟩ =
                          chartT '' CT ∧
                        localSideData.leftSidePiece ⟨itarget, htarget⟩ =
                          chartT '' RT ∧
                        localSideData.rightSidePiece ⟨itarget, htarget⟩ =
                          chartT '' LT)) := by
-- BODY
  obtain ⟨controlRadii, hr0, hr1, hsourceBalls, htargetBalls⟩ :=
    PolygonalArcCollarControlRadiiExistsBelow Aarc eta r0 r1 heta
      hIso.source_pos hIso.target_pos hIso
  obtain ⟨middleSegments⟩ :=
    PolygonalArcCollarMiddleSegmentDataExists Aarc controlRadii
  obtain ⟨forbiddenMargins⟩ :=
    PolygonalArcCollarMiddleForbiddenMarginsExists Aarc controlRadii
      middleSegments
  obtain ⟨compatibleTubes, hKinit, hKterm, _hsourceTube, _htargetTube⟩ :=
    PolygonalArcCollarCompatibleOrientedTubeDataExistsBelow Aarc controlRadii
      middleSegments forbiddenMargins r0 r1 K0 K1 hIso hK0 hK1
  obtain ⟨vertexLocalPieces, localTopology, hsourceOmit, htargetOmit,
      hsourceCone, htargetCone, _hsourceLeft, _htargetLeft,
      _hsourceRight, _htargetRight, hsourceCore, hsourceLeft,
      hsourceRight, htargetCore, htargetLeft, htargetRight⟩ :=
    PolygonalArcCollarLocalTopologyDataWithEndpointCaps Aarc controlRadii
      middleSegments forbiddenMargins compatibleTubes r0 r1 K0 K1
      hIso.source_pos hIso.target_pos hK0 hK1 hr0 hr1 hKinit hKterm
  obtain ⟨localSideData, hvertexCollarEq, hleftSidePieceEq,
      hrightSidePieceEq⟩ :=
    PolygonalArcCollarLocalSideDataOfLocalTopologyData Aarc controlRadii
      middleSegments forbiddenMargins compatibleTubes vertexLocalPieces
      localTopology
  obtain ⟨S, hcollar, hleft, hright, hnear⟩ :=
    PolygonalArcSideStripAssembly Aarc controlRadii middleSegments
      forbiddenMargins compatibleTubes.orientedTubes vertexLocalPieces
      localSideData
  refine ⟨controlRadii, middleSegments, forbiddenMargins, compatibleTubes,
    vertexLocalPieces, localSideData, S, ?_⟩
  dsimp
  refine ⟨hr0, hr1, hKinit, hKterm, hsourceBalls, htargetBalls,
    ?_, ?_, ?_, ?_, hcollar, hleft, hright, hnear,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [hvertexCollarEq] using hsourceOmit
  · simpa [hvertexCollarEq] using htargetOmit
  · simpa [hvertexCollarEq] using hsourceCone
  · simpa [hvertexCollarEq] using htargetCone
  · exact (hvertexCollarEq _).trans hsourceCore
  · exact (hleftSidePieceEq _).trans hsourceLeft
  · exact (hrightSidePieceEq _).trans hsourceRight
  · exact (hvertexCollarEq _).trans htargetCore
  · exact (hleftSidePieceEq _).trans htargetLeft
  · exact (hrightSidePieceEq _).trans htargetRight
