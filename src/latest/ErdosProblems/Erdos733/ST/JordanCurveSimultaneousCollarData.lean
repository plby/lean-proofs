import ErdosProblems.Erdos733.ST.SimpleClosedPolygonalCurve
import ErdosProblems.Erdos733.ST.FinitePolygonalSet
import ErdosProblems.Erdos733.ST.PolygonalArcCollarCompatibleOrientedTubeData
import ErdosProblems.Erdos733.ST.PolygonalArcCollarLocalSideData
import ErdosProblems.Erdos733.ST.PolygonalArcEndpointIsolation
import ErdosProblems.Erdos733.ST.PolygonalArcInitialEndpointLeftCone
import ErdosProblems.Erdos733.ST.PolygonalArcReverse
import ErdosProblems.Erdos733.ST.PolygonalArcTerminalEndpointLeftCone
import ErdosProblems.Erdos733.ST.PolygonalSideStrips

open Classical
noncomputable section

-- [TABLET NODE: JordanCurveSimultaneousCollarData]
structure JordanCurveSimultaneousCollarData (J : SimpleClosedPolygonalCurve) where
-- BODY
  presentation : FinitePolygonalSet
  presentation_carrier_eq : presentation.carrier = J.carrier
  vertexRadius : {gamma // gamma ∈ J.edgeArcs} → ℝ
  vertexRadius_pos : ∀ gamma, 0 < vertexRadius gamma
  vertexClosedDisks_disjoint :
    ∀ gamma delta : {gamma // gamma ∈ J.edgeArcs}, gamma ≠ delta →
      Disjoint (Metric.closedBall gamma.1.target (vertexRadius gamma))
        (Metric.closedBall delta.1.target (vertexRadius delta))
  endpointIsolation :
    ∀ gamma : {gamma // gamma ∈ J.edgeArcs},
      PolygonalArcEndpointIsolation gamma.1
        (vertexRadius (J.successor.symm gamma)) (vertexRadius gamma)
  vertexDisk_curve_eq :
    ∀ gamma : {gamma // gamma ∈ J.edgeArcs},
      Metric.ball gamma.1.target (vertexRadius gamma) ∩ J.carrier =
        Metric.ball gamma.1.target (vertexRadius gamma) ∩
          (gamma.1.carrier ∪ (J.successor gamma).1.carrier)
  leftVertexSector :
    {gamma // gamma ∈ J.edgeArcs} → Set (EuclideanSpace ℝ (Fin 2))
  rightVertexSector :
    {gamma // gamma ∈ J.edgeArcs} → Set (EuclideanSpace ℝ (Fin 2))
  leftVertexSector_nonempty : ∀ gamma, (leftVertexSector gamma).Nonempty
  rightVertexSector_nonempty : ∀ gamma, (rightVertexSector gamma).Nonempty
  leftVertexSector_open : ∀ gamma, IsOpen (leftVertexSector gamma)
  rightVertexSector_open : ∀ gamma, IsOpen (rightVertexSector gamma)
  leftVertexSector_connected : ∀ gamma, IsConnected (leftVertexSector gamma)
  rightVertexSector_connected : ∀ gamma, IsConnected (rightVertexSector gamma)
  leftVertexSector_subset_disk :
    ∀ gamma, leftVertexSector gamma ⊆
      Metric.ball gamma.1.target (vertexRadius gamma)
  rightVertexSector_subset_disk :
    ∀ gamma, rightVertexSector gamma ⊆
      Metric.ball gamma.1.target (vertexRadius gamma)
  leftVertexSector_subset_complement :
    ∀ gamma, leftVertexSector gamma ⊆ J.carrierᶜ
  rightVertexSector_subset_complement :
    ∀ gamma, rightVertexSector gamma ⊆ J.carrierᶜ
  vertexSectors_disjoint :
    ∀ gamma, Disjoint (leftVertexSector gamma) (rightVertexSector gamma)
  vertexDisk_complement_partition :
    ∀ gamma,
      Metric.ball gamma.1.target (vertexRadius gamma) \ J.carrier =
        leftVertexSector gamma ∪ rightVertexSector gamma
  vertex_mem_leftSector_closure :
    ∀ gamma, gamma.1.target ∈ closure (leftVertexSector gamma)
  vertex_mem_rightSector_closure :
    ∀ gamma, gamma.1.target ∈ closure (rightVertexSector gamma)
  sourceAperture : {gamma // gamma ∈ J.edgeArcs} → ℝ
  targetAperture : {gamma // gamma ∈ J.edgeArcs} → ℝ
  sourceAperture_pos : ∀ gamma, 0 < sourceAperture gamma
  targetAperture_pos : ∀ gamma, 0 < targetAperture gamma
  terminalLeftCone_subset_leftSector :
    ∀ gamma,
      PolygonalArcTerminalEndpointLeftCone gamma.1
          (vertexRadius gamma) (targetAperture gamma) ⊆
        leftVertexSector gamma
  successorInitialLeftCone_subset_leftSector :
    ∀ gamma,
      PolygonalArcInitialEndpointLeftCone (J.successor gamma).1
          (vertexRadius gamma) (sourceAperture (J.successor gamma)) ⊆
        leftVertexSector gamma
  terminalRightCone_subset_rightSector :
    ∀ gamma,
      PolygonalArcInitialEndpointLeftCone (PolygonalArcReverse gamma.1)
          (vertexRadius gamma) (targetAperture gamma) ⊆
        rightVertexSector gamma
  successorInitialRightCone_subset_rightSector :
    ∀ gamma,
      PolygonalArcTerminalEndpointLeftCone
          (PolygonalArcReverse (J.successor gamma).1)
          (vertexRadius gamma) (sourceAperture (J.successor gamma)) ⊆
        rightVertexSector gamma
  eta : {gamma // gamma ∈ J.edgeArcs} → ℝ
  eta_pos : ∀ gamma, 0 < eta gamma
  eta_lt_sourceRadius :
    ∀ gamma, eta gamma < vertexRadius (J.successor.symm gamma)
  eta_lt_targetRadius : ∀ gamma, eta gamma < vertexRadius gamma
  controlRadii :
    ∀ gamma : {gamma // gamma ∈ J.edgeArcs},
      PolygonalArcCollarControlRadii gamma.1 (eta gamma)
  source_controlRadius_lt :
    ∀ (gamma : {gamma // gamma ∈ J.edgeArcs})
      (hsource : 0 < gamma.1.vertices.length),
        (controlRadii gamma).radius ⟨0, hsource⟩ <
          vertexRadius (J.successor.symm gamma)
  target_controlRadius_lt :
    ∀ (gamma : {gamma // gamma ∈ J.edgeArcs})
      (htarget : gamma.1.vertices.length - 1 < gamma.1.vertices.length),
        (controlRadii gamma).radius
          ⟨gamma.1.vertices.length - 1, htarget⟩ < vertexRadius gamma
  source_controlBall_disjoint :
    ∀ (gamma : {gamma // gamma ∈ J.edgeArcs})
      (i : Fin gamma.1.vertices.length), i.1 ≠ 0 →
        Disjoint
          (Metric.ball gamma.1.vertices[i.1] ((controlRadii gamma).radius i))
          (Metric.ball gamma.1.source
            (vertexRadius (J.successor.symm gamma)))
  target_controlBall_disjoint :
    ∀ (gamma : {gamma // gamma ∈ J.edgeArcs})
      (i : Fin gamma.1.vertices.length),
        i.1 + 1 ≠ gamma.1.vertices.length →
          Disjoint
            (Metric.ball gamma.1.vertices[i.1] ((controlRadii gamma).radius i))
            (Metric.ball gamma.1.target (vertexRadius gamma))
  middleSegments :
    ∀ gamma : {gamma // gamma ∈ J.edgeArcs},
      PolygonalArcCollarMiddleSegmentData gamma.1 (controlRadii gamma)
  forbiddenMargins :
    ∀ gamma : {gamma // gamma ∈ J.edgeArcs},
      PolygonalArcCollarMiddleForbiddenMargins gamma.1 (controlRadii gamma)
        (middleSegments gamma)
  compatibleTubes :
    ∀ gamma : {gamma // gamma ∈ J.edgeArcs},
      PolygonalArcCollarCompatibleOrientedTubeData gamma.1 (controlRadii gamma)
        (middleSegments gamma) (forbiddenMargins gamma)
  initialConeBound_lt_sourceAperture :
    ∀ (gamma : {gamma // gamma ∈ J.edgeArcs})
      (hfirst : 0 + 1 < gamma.1.vertices.length),
        (compatibleTubes gamma).initialConeBound 0 hfirst <
          sourceAperture gamma
  terminalConeBound_lt_targetAperture :
    ∀ (gamma : {gamma // gamma ∈ J.edgeArcs})
      (hlast : (gamma.1.vertices.length - 2) + 1 < gamma.1.vertices.length),
        (compatibleTubes gamma).terminalConeBound
          (gamma.1.vertices.length - 2) hlast < targetAperture gamma
  vertexLocalPieces :
    ∀ gamma : {gamma // gamma ∈ J.edgeArcs},
      PolygonalArcCollarVertexLocalPieceData gamma.1 (controlRadii gamma)
        (middleSegments gamma) (forbiddenMargins gamma)
        (compatibleTubes gamma).orientedTubes.toPolygonalArcCollarSeparatedTubeData
  localSideData :
    ∀ gamma : {gamma // gamma ∈ J.edgeArcs},
      PolygonalArcCollarLocalSideData gamma.1 (controlRadii gamma)
        (middleSegments gamma) (forbiddenMargins gamma)
        (compatibleTubes gamma).orientedTubes (vertexLocalPieces gamma)
  source_leftPiece_subset_initialCone :
    ∀ (gamma : {gamma // gamma ∈ J.edgeArcs})
      (hsource : 0 < gamma.1.vertices.length),
        (localSideData gamma).leftSidePiece ⟨0, hsource⟩ ⊆
          PolygonalArcInitialEndpointLeftCone gamma.1
            (vertexRadius (J.successor.symm gamma)) (sourceAperture gamma)
  target_leftPiece_subset_terminalCone :
    ∀ (gamma : {gamma // gamma ∈ J.edgeArcs})
      (htarget : gamma.1.vertices.length - 1 < gamma.1.vertices.length),
        (localSideData gamma).leftSidePiece
            ⟨gamma.1.vertices.length - 1, htarget⟩ ⊆
          PolygonalArcTerminalEndpointLeftCone gamma.1
            (vertexRadius gamma) (targetAperture gamma)
  source_rightPiece_subset_reverseCone :
    ∀ (gamma : {gamma // gamma ∈ J.edgeArcs})
      (hsource : 0 < gamma.1.vertices.length),
        (localSideData gamma).rightSidePiece ⟨0, hsource⟩ ⊆
          PolygonalArcTerminalEndpointLeftCone (PolygonalArcReverse gamma.1)
            (vertexRadius (J.successor.symm gamma)) (sourceAperture gamma)
  target_rightPiece_subset_reverseCone :
    ∀ (gamma : {gamma // gamma ∈ J.edgeArcs})
      (htarget : gamma.1.vertices.length - 1 < gamma.1.vertices.length),
        (localSideData gamma).rightSidePiece
            ⟨gamma.1.vertices.length - 1, htarget⟩ ⊆
          PolygonalArcInitialEndpointLeftCone (PolygonalArcReverse gamma.1)
            (vertexRadius gamma) (targetAperture gamma)
  sideStrips :
    ∀ gamma : {gamma // gamma ∈ J.edgeArcs}, PolygonalSideStrips gamma.1
  localLeftPiece_subset_leftStrip :
    ∀ (gamma : {gamma // gamma ∈ J.edgeArcs})
      (i : Fin gamma.1.vertices.length),
        (localSideData gamma).leftSidePiece i ⊆ (sideStrips gamma).leftStrip
  localRightPiece_subset_rightStrip :
    ∀ (gamma : {gamma // gamma ∈ J.edgeArcs})
      (i : Fin gamma.1.vertices.length),
        (localSideData gamma).rightSidePiece i ⊆ (sideStrips gamma).rightStrip
  collar_near_edgeArc :
    ∀ (gamma : {gamma // gamma ∈ J.edgeArcs}) (z : EuclideanSpace ℝ (Fin 2)),
      z ∈ (sideStrips gamma).collar →
        ∃ p ∈ gamma.1.carrier, dist z p < eta gamma
  collar_disjoint_other_edgeArcs :
    ∀ gamma delta : {gamma // gamma ∈ J.edgeArcs}, delta ≠ gamma →
      Disjoint (sideStrips gamma).collar delta.1.carrier
  leftStrip_subset_curve_complement :
    ∀ gamma, (sideStrips gamma).leftStrip ⊆ J.carrierᶜ
  rightStrip_subset_curve_complement :
    ∀ gamma, (sideStrips gamma).rightStrip ⊆ J.carrierᶜ
  leftSector_meets_terminalStrip :
    ∀ gamma,
      (leftVertexSector gamma ∩ (sideStrips gamma).leftStrip).Nonempty
  leftSector_meets_successorInitialStrip :
    ∀ gamma,
      (leftVertexSector gamma ∩
        (sideStrips (J.successor gamma)).leftStrip).Nonempty
  rightSector_meets_terminalStrip :
    ∀ gamma,
      (rightVertexSector gamma ∩ (sideStrips gamma).rightStrip).Nonempty
  rightSector_meets_successorInitialStrip :
    ∀ gamma,
      (rightVertexSector gamma ∩
        (sideStrips (J.successor gamma)).rightStrip).Nonempty
