import ErdosProblems.Erdos733.ST.OrdinaryDrawingImage
import ErdosProblems.Erdos733.ST.OrdinaryDrawingImageWithoutEdge
import ErdosProblems.Erdos733.ST.PlaneDrawingDartVertexSectorGeometry
import ErdosProblems.Erdos733.ST.PolygonalArcCollarCompatibleOrientedTubeData
import ErdosProblems.Erdos733.ST.PolygonalArcCollarLocalSideData
import ErdosProblems.Erdos733.ST.PolygonalArcEndpointIsolation
import ErdosProblems.Erdos733.ST.PolygonalArcInitialEndpointLeftCone
import ErdosProblems.Erdos733.ST.PolygonalArcSideStripAssembly
import ErdosProblems.Erdos733.ST.PolygonalArcTerminalEndpointLeftCone
import ErdosProblems.Erdos733.ST.PolygonalSideStrips
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

open Classical
noncomputable section

-- [TABLET NODE: PlaneDrawingDartCollarChoiceData]
structure PlaneDrawingDartCollarChoiceData {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet] [DecidableRel G.Adj]
    (D : OrdinaryPolygonalDrawing G) (A : PlaneDrawingDartArcData G D)
    (C : PlaneDrawingDartVertexSectorGeometry G D A) where
-- BODY
  sourceRadius : G.Dart → ℝ
  targetRadius : G.Dart → ℝ
  endpointIsolation :
    ∀ d : G.Dart, PolygonalArcEndpointIsolation (A.dartArc d)
      (sourceRadius d) (targetRadius d)
  sourceRadius_lt_localDisk :
    ∀ d : G.Dart, sourceRadius d < C.star.localDiskRadius d.toProd.1
  targetRadius_lt_localDisk :
    ∀ d : G.Dart, targetRadius d < C.star.localDiskRadius d.toProd.2
  sourceAperture : G.Dart → ℝ
  targetAperture : G.Dart → ℝ
  sourceAperture_pos : ∀ d : G.Dart, 0 < sourceAperture d
  targetAperture_pos : ∀ d : G.Dart, 0 < targetAperture d
  terminalSectorRadius : G.Dart → ℝ
  terminalSectorAperture : G.Dart → ℝ
  terminalSectorRadius_pos : ∀ d : G.Dart, 0 < terminalSectorRadius d
  terminalSectorAperture_pos : ∀ d : G.Dart, 0 < terminalSectorAperture d
  terminalSector_subset_successorSector :
    ∀ d : G.Dart,
      PolygonalArcTerminalEndpointLeftCone (A.dartArc d)
        (terminalSectorRadius d) (terminalSectorAperture d) ⊆
          C.successorSector d
  successorInitialSectorRadius : G.Dart → ℝ
  successorInitialSectorAperture : G.Dart → ℝ
  successorInitialSectorRadius_pos :
    ∀ d : G.Dart, 0 < successorInitialSectorRadius d
  successorInitialSectorAperture_pos :
    ∀ d : G.Dart, 0 < successorInitialSectorAperture d
  successorInitialSector_subset_successorSector :
    ∀ d : G.Dart,
      PolygonalArcInitialEndpointLeftCone (A.dartArc (C.star.successor d))
        (successorInitialSectorRadius d) (successorInitialSectorAperture d) ⊆
          C.successorSector d
  targetRadius_lt_terminalSectorRadius :
    ∀ d : G.Dart, targetRadius d < terminalSectorRadius d
  targetAperture_lt_terminalSectorAperture :
    ∀ d : G.Dart, targetAperture d < terminalSectorAperture d
  successor_sourceRadius_lt_initialSectorRadius :
    ∀ d : G.Dart, sourceRadius (C.star.successor d) <
      successorInitialSectorRadius d
  successor_sourceAperture_lt_initialSectorAperture :
    ∀ d : G.Dart, sourceAperture (C.star.successor d) <
      successorInitialSectorAperture d
  eta : G.Dart → ℝ
  eta_pos : ∀ d : G.Dart, 0 < eta d
  eta_lt_sourceRadius : ∀ d : G.Dart, eta d < sourceRadius d
  eta_lt_targetRadius : ∀ d : G.Dart, eta d < targetRadius d
  awaySeparation : G.Dart → ℝ
  awaySeparation_pos : ∀ d : G.Dart, 0 < awaySeparation d
  eta_lt_awaySeparation : ∀ d : G.Dart, eta d < awaySeparation d
  awaySeparation_le_dist :
    ∀ (d : G.Dart) (x : EuclideanSpace ℝ (Fin 2)),
      x ∈ OrdinaryDrawingImageWithoutEdge G D (A.dartEdge d) →
        x ∉ Metric.ball (A.dartArc d).source (sourceRadius d) ∪
          Metric.ball (A.dartArc d).target (targetRadius d) →
          ∀ p : EuclideanSpace ℝ (Fin 2),
            p ∈ (A.dartArc d).carrier →
              awaySeparation d ≤ dist x p
  controlRadii :
    ∀ d : G.Dart, PolygonalArcCollarControlRadii (A.dartArc d) (eta d)
  source_controlRadius_lt :
    ∀ (d : G.Dart) (hsource : 0 < (A.dartArc d).vertices.length),
      (controlRadii d).radius ⟨0, hsource⟩ < sourceRadius d
  target_controlRadius_lt :
    ∀ (d : G.Dart)
      (htarget : (A.dartArc d).vertices.length - 1 <
        (A.dartArc d).vertices.length),
      (controlRadii d).radius
        ⟨(A.dartArc d).vertices.length - 1, htarget⟩ < targetRadius d
  source_controlBall_disjoint :
    ∀ (d : G.Dart) (i : Fin (A.dartArc d).vertices.length),
      i.1 ≠ 0 →
        Disjoint
          (Metric.ball (A.dartArc d).vertices[i.1] ((controlRadii d).radius i))
          (Metric.ball (A.dartArc d).source (sourceRadius d))
  target_controlBall_disjoint :
    ∀ (d : G.Dart) (i : Fin (A.dartArc d).vertices.length),
      i.1 + 1 ≠ (A.dartArc d).vertices.length →
        Disjoint
          (Metric.ball (A.dartArc d).vertices[i.1] ((controlRadii d).radius i))
          (Metric.ball (A.dartArc d).target (targetRadius d))
  middleSegments :
    ∀ d : G.Dart,
      PolygonalArcCollarMiddleSegmentData (A.dartArc d) (controlRadii d)
  forbiddenMargins :
    ∀ d : G.Dart,
      PolygonalArcCollarMiddleForbiddenMargins (A.dartArc d) (controlRadii d)
        (middleSegments d)
  compatibleTubes :
    ∀ d : G.Dart,
      PolygonalArcCollarCompatibleOrientedTubeData (A.dartArc d)
        (controlRadii d) (middleSegments d) (forbiddenMargins d)
  initialConeBound_lt_sourceAperture :
    ∀ (d : G.Dart) (hfirst : 0 + 1 < (A.dartArc d).vertices.length),
      (compatibleTubes d).initialConeBound 0 hfirst < sourceAperture d
  terminalConeBound_lt_targetAperture :
    ∀ (d : G.Dart)
      (hlast : ((A.dartArc d).vertices.length - 2) + 1 <
        (A.dartArc d).vertices.length),
      (compatibleTubes d).terminalConeBound ((A.dartArc d).vertices.length - 2)
        hlast < targetAperture d
  nonfirst_tube_disjoint_sourceBall :
    ∀ (d : G.Dart) (j : ℕ) (hj : j + 1 < (A.dartArc d).vertices.length),
      j ≠ 0 →
        Disjoint ((compatibleTubes d).orientedTubes.tube j hj)
          (Metric.ball (A.dartArc d).source (sourceRadius d))
  nonlast_tube_disjoint_targetBall :
    ∀ (d : G.Dart) (j : ℕ) (hj : j + 1 < (A.dartArc d).vertices.length),
      (j + 1) + 1 ≠ (A.dartArc d).vertices.length →
        Disjoint ((compatibleTubes d).orientedTubes.tube j hj)
          (Metric.ball (A.dartArc d).target (targetRadius d))
  first_leftHalf_sourceBall_subset_initialCone :
    ∀ (d : G.Dart) (hfirst : 0 + 1 < (A.dartArc d).vertices.length),
      (compatibleTubes d).orientedTubes.leftHalf 0 hfirst ∩
          Metric.ball (A.dartArc d).source (sourceRadius d) ⊆
        PolygonalArcInitialEndpointLeftCone (A.dartArc d)
          (sourceRadius d) (sourceAperture d)
  last_leftHalf_targetBall_subset_terminalCone :
    ∀ (d : G.Dart)
      (hlast : ((A.dartArc d).vertices.length - 2) + 1 <
        (A.dartArc d).vertices.length),
      (compatibleTubes d).orientedTubes.leftHalf
          ((A.dartArc d).vertices.length - 2) hlast ∩
          Metric.ball (A.dartArc d).target (targetRadius d) ⊆
        PolygonalArcTerminalEndpointLeftCone (A.dartArc d)
          (targetRadius d) (targetAperture d)
  vertexLocalPieces :
    ∀ d : G.Dart,
      PolygonalArcCollarVertexLocalPieceData (A.dartArc d) (controlRadii d)
        (middleSegments d) (forbiddenMargins d)
        (compatibleTubes d).orientedTubes.toPolygonalArcCollarSeparatedTubeData
  localSideData :
    ∀ d : G.Dart,
      PolygonalArcCollarLocalSideData (A.dartArc d) (controlRadii d)
        (middleSegments d) (forbiddenMargins d)
        (compatibleTubes d).orientedTubes (vertexLocalPieces d)
  source_leftSidePiece_subset_initialCone :
    ∀ (d : G.Dart) (hsource : 0 < (A.dartArc d).vertices.length),
      (localSideData d).leftSidePiece ⟨0, hsource⟩ ⊆
        PolygonalArcInitialEndpointLeftCone (A.dartArc d)
          (sourceRadius d) (sourceAperture d)
  target_leftSidePiece_subset_terminalCone :
    ∀ (d : G.Dart)
      (htarget : (A.dartArc d).vertices.length - 1 <
        (A.dartArc d).vertices.length),
      (localSideData d).leftSidePiece
        ⟨(A.dartArc d).vertices.length - 1, htarget⟩ ⊆
          PolygonalArcTerminalEndpointLeftCone (A.dartArc d)
            (targetRadius d) (targetAperture d)
  sideStrips : ∀ d : G.Dart, PolygonalSideStrips (A.dartArc d)
  leftStrip_nonempty :
    ∀ d : G.Dart, ((sideStrips d).leftStrip).Nonempty
  leftStrip_subset_complement :
    ∀ d : G.Dart,
      (sideStrips d).leftStrip ⊆ (OrdinaryDrawingImage G D)ᶜ
  localComplement_subset_sideStrips :
    ∀ (d : G.Dart) (x : EuclideanSpace ℝ (Fin 2)),
      x ∈ (A.dartArc d).relativeInterior →
        ∃ U : Set (EuclideanSpace ℝ (Fin 2)),
          IsOpen U ∧ x ∈ U ∧
            U ∩ (OrdinaryDrawingImage G D)ᶜ ⊆
              (sideStrips d).leftStrip ∪ (sideStrips d.symm).leftStrip
  rightStrip_eq_leftStrip_symm :
    ∀ d : G.Dart, (sideStrips d).rightStrip = (sideStrips d.symm).leftStrip
  successorSector_meets_leftStrip :
    ∀ d : G.Dart,
      (C.successorSector d ∩ (sideStrips d).leftStrip ∩
        Metric.ball (D.vertexPlacement d.toProd.2)
          (C.star.localDiskRadius d.toProd.2)).Nonempty
  successorSector_meets_successor_leftStrip :
    ∀ d : G.Dart,
      (C.successorSector d ∩ (sideStrips (C.star.successor d)).leftStrip ∩
        Metric.ball (D.vertexPlacement d.toProd.2)
          (C.star.localDiskRadius d.toProd.2)).Nonempty
