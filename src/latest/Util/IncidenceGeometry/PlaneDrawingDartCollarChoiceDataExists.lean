import Util.IncidenceGeometry.OrdinaryDrawingImage
import Util.IncidenceGeometry.OrdinaryDrawingImageWithoutEdge
import Util.IncidenceGeometry.PlaneDrawingDartArcEndpointAwaySeparation
import Util.IncidenceGeometry.PlaneDrawingDartArcData
import Util.IncidenceGeometry.PlaneDrawingDartCollarChoiceData
import Util.IncidenceGeometry.PlaneDrawingDartCoherentSideStripsExist
import Util.IncidenceGeometry.PlaneDrawingDartVertexSectorGeometry
import Util.IncidenceGeometry.PlaneDrawingDartVertexStarData
import Util.IncidenceGeometry.PlaneDrawingSelectedEdgeAwayFromEndpointCompact
import Util.IncidenceGeometry.PolygonalArc
import Util.IncidenceGeometry.PolygonalArcCarrierCompact
import Util.IncidenceGeometry.PolygonalArcCollarCompatibleOrientedTubeDataExistsBelow
import Util.IncidenceGeometry.PolygonalArcCollarControlRadiiExistsBelow
import Util.IncidenceGeometry.PolygonalArcCollarLocalSideData
import Util.IncidenceGeometry.PolygonalArcCollarLocalSideDataExistsWithEndpointLeftCones
import Util.IncidenceGeometry.PolygonalArcCollarMiddleForbiddenMarginsExists
import Util.IncidenceGeometry.PolygonalArcCollarMiddleSegmentDataExists
import Util.IncidenceGeometry.PolygonalArcCollarVertexLocalPieceData
import Util.IncidenceGeometry.PolygonalArcEndpointIsolation
import Util.IncidenceGeometry.PolygonalArcEndpointIsolationExists
import Util.IncidenceGeometry.PolygonalArcEndpointLeftHalfTubeSubsetLeftCones
import Util.IncidenceGeometry.PolygonalArcInitialEndpointLeftCone
import Util.IncidenceGeometry.PolygonalArcOpenSegmentSubsetRelativeInterior
import Util.IncidenceGeometry.PolygonalArcSideStripAssembly
import Util.IncidenceGeometry.PolygonalArcTerminalEndpointLeftCone
import Util.IncidenceGeometry.PolygonalSideStrips
import Util.IncidenceGeometry.PolygonalSideStripsReverseOfSameCarrier
import Util.IncidenceGeometry.PositiveSeparation
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

open Classical
noncomputable section

lemma PlaneDrawingDartCollarChoiceDataExists {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet] [DecidableRel G.Adj]
    (D : OrdinaryPolygonalDrawing G) (hD : D.crossingSet.card = 0)
    (A : PlaneDrawingDartArcData G D)
    (C : PlaneDrawingDartVertexSectorGeometry G D A) :
    Nonempty (PlaneDrawingDartCollarChoiceData G D A C) := by
  let terminalSectorRadius : G.Dart → ℝ := fun d =>
    Classical.choose (C.terminal_left_endpoint_sector_access d)
  let terminalSectorAperture : G.Dart → ℝ := fun d =>
    Classical.choose
      (Classical.choose_spec (C.terminal_left_endpoint_sector_access d))
  have hterminalSpec :
      ∀ d : G.Dart,
        0 < terminalSectorRadius d ∧ 0 < terminalSectorAperture d ∧
          PolygonalArcTerminalEndpointLeftCone (A.dartArc d)
            (terminalSectorRadius d) (terminalSectorAperture d) ⊆
              C.successorSector d := by
    intro d
    dsimp [terminalSectorRadius, terminalSectorAperture]
    exact Classical.choose_spec
      (Classical.choose_spec (C.terminal_left_endpoint_sector_access d))
  let successorInitialSectorRadius : G.Dart → ℝ := fun d =>
    Classical.choose (C.successor_initial_left_endpoint_sector_access d)
  let successorInitialSectorAperture : G.Dart → ℝ := fun d =>
    Classical.choose
      (Classical.choose_spec (C.successor_initial_left_endpoint_sector_access d))
  have hsuccessorInitialSpec :
      ∀ d : G.Dart,
        0 < successorInitialSectorRadius d ∧
          0 < successorInitialSectorAperture d ∧
            PolygonalArcInitialEndpointLeftCone (A.dartArc (C.star.successor d))
              (successorInitialSectorRadius d)
                (successorInitialSectorAperture d) ⊆
                  C.successorSector d := by
    intro d
    dsimp [successorInitialSectorRadius, successorInitialSectorAperture]
    exact Classical.choose_spec
      (Classical.choose_spec (C.successor_initial_left_endpoint_sector_access d))
  let baseSourceRadius : G.Dart → ℝ := fun d =>
    Classical.choose (PolygonalArcEndpointIsolationExists (A.dartArc d))
  let baseTargetRadius : G.Dart → ℝ := fun d =>
    Classical.choose
      (Classical.choose_spec (PolygonalArcEndpointIsolationExists (A.dartArc d)))
  have hbaseIsolation :
      ∀ d : G.Dart,
        PolygonalArcEndpointIsolation (A.dartArc d)
          (baseSourceRadius d) (baseTargetRadius d) := by
    intro d
    dsimp [baseSourceRadius, baseTargetRadius]
    exact Classical.choose_spec
      (Classical.choose_spec (PolygonalArcEndpointIsolationExists (A.dartArc d)))
  let sourceBound : G.Dart → ℝ := fun d =>
    min (baseSourceRadius d)
      (min (C.star.localDiskRadius d.toProd.1)
        (successorInitialSectorRadius (C.star.successor.symm d)))
  let targetBound : G.Dart → ℝ := fun d =>
    min (baseTargetRadius d)
      (min (C.star.localDiskRadius d.toProd.2) (terminalSectorRadius d))
  let sourceRadius : G.Dart → ℝ := fun d => sourceBound d / 2
  let targetRadius : G.Dart → ℝ := fun d => targetBound d / 2
  have hsourceBound_pos : ∀ d : G.Dart, 0 < sourceBound d := by
    intro d
    dsimp [sourceBound]
    exact lt_min (hbaseIsolation d).source_pos
      (lt_min (C.star.localDiskRadius_pos d.toProd.1)
        (hsuccessorInitialSpec (C.star.successor.symm d)).1)
  have htargetBound_pos : ∀ d : G.Dart, 0 < targetBound d := by
    intro d
    dsimp [targetBound]
    exact lt_min (hbaseIsolation d).target_pos
      (lt_min (C.star.localDiskRadius_pos d.toProd.2) (hterminalSpec d).1)
  have hsourceRadius_pos : ∀ d : G.Dart, 0 < sourceRadius d := by
    intro d
    dsimp [sourceRadius]
    nlinarith [hsourceBound_pos d]
  have htargetRadius_pos : ∀ d : G.Dart, 0 < targetRadius d := by
    intro d
    dsimp [targetRadius]
    nlinarith [htargetBound_pos d]
  have hsourceRadius_le_base :
      ∀ d : G.Dart, sourceRadius d ≤ baseSourceRadius d := by
    intro d
    dsimp [sourceRadius]
    have hle : sourceBound d ≤ baseSourceRadius d := by
      dsimp [sourceBound]
      exact min_le_left _ _
    nlinarith [hsourceBound_pos d]
  have htargetRadius_le_base :
      ∀ d : G.Dart, targetRadius d ≤ baseTargetRadius d := by
    intro d
    dsimp [targetRadius]
    have hle : targetBound d ≤ baseTargetRadius d := by
      dsimp [targetBound]
      exact min_le_left _ _
    nlinarith [htargetBound_pos d]
  have hsourceRadius_lt_localDisk :
      ∀ d : G.Dart, sourceRadius d < C.star.localDiskRadius d.toProd.1 := by
    intro d
    dsimp [sourceRadius]
    have hle : sourceBound d ≤ C.star.localDiskRadius d.toProd.1 := by
      dsimp [sourceBound]
      exact le_trans (min_le_right _ _) (min_le_left _ _)
    nlinarith [hsourceBound_pos d]
  have htargetRadius_lt_localDisk :
      ∀ d : G.Dart, targetRadius d < C.star.localDiskRadius d.toProd.2 := by
    intro d
    dsimp [targetRadius]
    have hle : targetBound d ≤ C.star.localDiskRadius d.toProd.2 := by
      dsimp [targetBound]
      exact le_trans (min_le_right _ _) (min_le_left _ _)
    nlinarith [htargetBound_pos d]
  have hsourceRadius_lt_successorInitial :
      ∀ d : G.Dart,
        sourceRadius d <
          successorInitialSectorRadius (C.star.successor.symm d) := by
    intro d
    dsimp [sourceRadius]
    have hle :
        sourceBound d ≤
          successorInitialSectorRadius (C.star.successor.symm d) := by
      dsimp [sourceBound]
      exact le_trans (min_le_right _ _) (min_le_right _ _)
    nlinarith [hsourceBound_pos d]
  have htargetRadius_lt_terminal :
      ∀ d : G.Dart, targetRadius d < terminalSectorRadius d := by
    intro d
    dsimp [targetRadius]
    have hle : targetBound d ≤ terminalSectorRadius d := by
      dsimp [targetBound]
      exact le_trans (min_le_right _ _) (min_le_right _ _)
    nlinarith [htargetBound_pos d]
  let sourceAperture : G.Dart → ℝ := fun d =>
    successorInitialSectorAperture (C.star.successor.symm d) / 2
  let targetAperture : G.Dart → ℝ := fun d =>
    terminalSectorAperture d / 2
  have hsourceAperture_pos : ∀ d : G.Dart, 0 < sourceAperture d := by
    intro d
    dsimp [sourceAperture]
    nlinarith [(hsuccessorInitialSpec (C.star.successor.symm d)).2.1]
  have htargetAperture_pos : ∀ d : G.Dart, 0 < targetAperture d := by
    intro d
    dsimp [targetAperture]
    nlinarith [(hterminalSpec d).2.1]
  have hsourceAperture_lt_successorInitial :
      ∀ d : G.Dart,
        sourceAperture d <
          successorInitialSectorAperture (C.star.successor.symm d) := by
    intro d
    dsimp [sourceAperture]
    nlinarith [(hsuccessorInitialSpec (C.star.successor.symm d)).2.1]
  have htargetAperture_lt_terminal :
      ∀ d : G.Dart, targetAperture d < terminalSectorAperture d := by
    intro d
    dsimp [targetAperture]
    nlinarith [(hterminalSpec d).2.1]
  have hendpointIsolation :
      ∀ d : G.Dart,
        PolygonalArcEndpointIsolation (A.dartArc d)
          (sourceRadius d) (targetRadius d) := by
    intro d
    let γ : PolygonalArc := A.dartArc d
    have hIsoBase := hbaseIsolation d
    have hsle := hsourceRadius_le_base d
    have htle := htargetRadius_le_base d
    refine
      { source_pos := hsourceRadius_pos d
        target_pos := htargetRadius_pos d
        source_lt_initial_length := lt_of_le_of_lt hsle
          hIsoBase.source_lt_initial_length
        target_lt_terminal_length := lt_of_le_of_lt htle
          hIsoBase.target_lt_terminal_length
        endpoint_closedBalls_disjoint := ?_
        source_closedBall_carrier_subset_initial_segment := ?_
        target_closedBall_carrier_subset_terminal_segment := ?_ }
    · exact Disjoint.mono
        (by
          intro x hx
          rw [Metric.mem_closedBall] at hx ⊢
          exact le_trans hx hsle)
        (by
          intro x hx
          rw [Metric.mem_closedBall] at hx ⊢
          exact le_trans hx htle)
        hIsoBase.endpoint_closedBalls_disjoint
    · change
        Metric.closedBall (A.dartArc d).source (sourceRadius d) ∩
            (A.dartArc d).carrier ⊆
          segment ℝ (A.dartArc d).source
            ((A.dartArc d).vertices[1]'(Nat.lt_of_succ_le
              (A.dartArc d).length_ge_two))
      intro x hx
      exact hIsoBase.source_closedBall_carrier_subset_initial_segment
        ⟨by
          have hxball : x ∈ Metric.closedBall (A.dartArc d).source
              (sourceRadius d) := hx.1
          rw [Metric.mem_closedBall] at hxball ⊢
          exact le_trans hxball hsle, hx.2⟩
    · let hprev : (A.dartArc d).vertices.length - 2 <
          (A.dartArc d).vertices.length := by
        have hlen := (A.dartArc d).length_ge_two
        omega
      change
        Metric.closedBall (A.dartArc d).target (targetRadius d) ∩
            (A.dartArc d).carrier ⊆
          segment ℝ (A.dartArc d).target
            ((A.dartArc d).vertices[(A.dartArc d).vertices.length - 2]'hprev)
      intro x hx
      exact hIsoBase.target_closedBall_carrier_subset_terminal_segment
        ⟨by
          have hxball : x ∈ Metric.closedBall (A.dartArc d).target
              (targetRadius d) := hx.1
          rw [Metric.mem_closedBall] at hxball ⊢
          exact le_trans hxball htle, hx.2⟩
  let awaySeparation : G.Dart → ℝ := fun d =>
    Classical.choose
      (PlaneDrawingDartArcEndpointAwaySeparation G D hD A d
        (sourceRadius d) (targetRadius d)
        (hsourceRadius_pos d) (htargetRadius_pos d))
  have hawaySpec :
      ∀ d : G.Dart,
        0 < awaySeparation d ∧
          ∀ x : EuclideanSpace ℝ (Fin 2),
            x ∈ OrdinaryDrawingImageWithoutEdge G D (A.dartEdge d) →
              x ∉ Metric.ball (A.dartArc d).source (sourceRadius d) ∪
                Metric.ball (A.dartArc d).target (targetRadius d) →
                ∀ p : EuclideanSpace ℝ (Fin 2),
                  p ∈ (A.dartArc d).carrier →
                    awaySeparation d ≤ dist x p := by
    intro d
    dsimp [awaySeparation]
    exact Classical.choose_spec
      (PlaneDrawingDartArcEndpointAwaySeparation G D hD A d
        (sourceRadius d) (targetRadius d)
        (hsourceRadius_pos d) (htargetRadius_pos d))
  let eta : G.Dart → ℝ := fun d =>
    min (awaySeparation d) (min (sourceRadius d) (targetRadius d)) / 2
  have heta_pos : ∀ d : G.Dart, 0 < eta d := by
    intro d
    dsimp [eta]
    have hminpos :
        0 < min (awaySeparation d) (min (sourceRadius d) (targetRadius d)) :=
      lt_min (hawaySpec d).1 (lt_min (hsourceRadius_pos d) (htargetRadius_pos d))
    nlinarith
  have heta_lt_away : ∀ d : G.Dart, eta d < awaySeparation d := by
    intro d
    dsimp [eta]
    have hminpos :
        0 < min (awaySeparation d) (min (sourceRadius d) (targetRadius d)) :=
      lt_min (hawaySpec d).1 (lt_min (hsourceRadius_pos d) (htargetRadius_pos d))
    have hle :
        min (awaySeparation d) (min (sourceRadius d) (targetRadius d)) ≤
          awaySeparation d := min_le_left _ _
    nlinarith
  have heta_lt_source : ∀ d : G.Dart, eta d < sourceRadius d := by
    intro d
    dsimp [eta]
    have hminpos :
        0 < min (awaySeparation d) (min (sourceRadius d) (targetRadius d)) :=
      lt_min (hawaySpec d).1 (lt_min (hsourceRadius_pos d) (htargetRadius_pos d))
    have hle :
        min (awaySeparation d) (min (sourceRadius d) (targetRadius d)) ≤
          sourceRadius d := by
      exact le_trans (min_le_right _ _) (min_le_left _ _)
    nlinarith
  have heta_lt_target : ∀ d : G.Dart, eta d < targetRadius d := by
    intro d
    dsimp [eta]
    have hminpos :
        0 < min (awaySeparation d) (min (sourceRadius d) (targetRadius d)) :=
      lt_min (hawaySpec d).1 (lt_min (hsourceRadius_pos d) (htargetRadius_pos d))
    have hle :
        min (awaySeparation d) (min (sourceRadius d) (targetRadius d)) ≤
          targetRadius d := by
      exact le_trans (min_le_right _ _) (min_le_right _ _)
    nlinarith
  let controlRadii :
      ∀ d : G.Dart, PolygonalArcCollarControlRadii (A.dartArc d) (eta d) :=
    fun d =>
      Classical.choose
        (PolygonalArcCollarControlRadiiExistsBelow (A.dartArc d)
          (eta d) (sourceRadius d) (targetRadius d)
          (heta_pos d) (hsourceRadius_pos d) (htargetRadius_pos d)
          (hendpointIsolation d))
  have hcontrolSpec :
      ∀ d : G.Dart,
        let γ := A.dartArc d
        let hsource : 0 < γ.vertices.length := by
          have hlen := γ.length_ge_two
          omega
        let htarget : γ.vertices.length - 1 < γ.vertices.length := by
          have hlen := γ.length_ge_two
          omega
        (controlRadii d).radius ⟨0, hsource⟩ < sourceRadius d ∧
          (controlRadii d).radius ⟨γ.vertices.length - 1, htarget⟩ <
            targetRadius d ∧
            (∀ i : Fin γ.vertices.length, i.1 ≠ 0 →
              Disjoint
                (Metric.ball γ.vertices[i.1] ((controlRadii d).radius i))
                (Metric.ball γ.source (sourceRadius d))) ∧
              (∀ i : Fin γ.vertices.length,
                i.1 + 1 ≠ γ.vertices.length →
                  Disjoint
                    (Metric.ball γ.vertices[i.1] ((controlRadii d).radius i))
                    (Metric.ball γ.target (targetRadius d))) := by
    intro d
    dsimp [controlRadii]
    exact Classical.choose_spec
      (PolygonalArcCollarControlRadiiExistsBelow (A.dartArc d)
        (eta d) (sourceRadius d) (targetRadius d)
        (heta_pos d) (hsourceRadius_pos d) (htargetRadius_pos d)
        (hendpointIsolation d))
  let middleSegments :
      ∀ d : G.Dart,
        PolygonalArcCollarMiddleSegmentData (A.dartArc d) (controlRadii d) :=
    fun d => Classical.choice
      (PolygonalArcCollarMiddleSegmentDataExists (A.dartArc d) (controlRadii d))
  let forbiddenMargins :
      ∀ d : G.Dart,
        PolygonalArcCollarMiddleForbiddenMargins (A.dartArc d)
          (controlRadii d) (middleSegments d) :=
    fun d => Classical.choice
      (PolygonalArcCollarMiddleForbiddenMarginsExists (A.dartArc d)
        (controlRadii d) (middleSegments d))
  let compatibleTubes :
      ∀ d : G.Dart,
        PolygonalArcCollarCompatibleOrientedTubeData (A.dartArc d)
          (controlRadii d) (middleSegments d) (forbiddenMargins d) :=
    fun d =>
      Classical.choose
        (PolygonalArcCollarCompatibleOrientedTubeDataExistsBelow (A.dartArc d)
          (controlRadii d) (middleSegments d) (forbiddenMargins d)
          (sourceRadius d) (targetRadius d) (sourceAperture d)
          (targetAperture d) (hendpointIsolation d) (hsourceAperture_pos d)
          (htargetAperture_pos d))
  have htubeSpec :
      ∀ d : G.Dart,
        let γ := A.dartArc d
        let hfirst : 0 + 1 < γ.vertices.length := by
          have hlen := γ.length_ge_two
          omega
        let jlast : ℕ := γ.vertices.length - 2
        let hlast : jlast + 1 < γ.vertices.length := by
          have hlen := γ.length_ge_two
          dsimp [jlast]
          omega
        (compatibleTubes d).initialConeBound 0 hfirst < sourceAperture d ∧
          (compatibleTubes d).terminalConeBound jlast hlast < targetAperture d ∧
            (∀ (j : ℕ) (hj : j + 1 < γ.vertices.length), j ≠ 0 →
              Disjoint
                (((compatibleTubes d).orientedTubes.toPolygonalArcCollarSeparatedTubeData).tube
                  j hj)
                (Metric.ball γ.source (sourceRadius d))) ∧
              (∀ (j : ℕ) (hj : j + 1 < γ.vertices.length), j ≠ jlast →
                Disjoint
                  (((compatibleTubes d).orientedTubes.toPolygonalArcCollarSeparatedTubeData).tube
                    j hj)
                  (Metric.ball γ.target (targetRadius d))) := by
    intro d
    dsimp [compatibleTubes]
    exact Classical.choose_spec
      (PolygonalArcCollarCompatibleOrientedTubeDataExistsBelow (A.dartArc d)
        (controlRadii d) (middleSegments d) (forbiddenMargins d)
        (sourceRadius d) (targetRadius d) (sourceAperture d)
        (targetAperture d) (hendpointIsolation d) (hsourceAperture_pos d)
        (htargetAperture_pos d))
  let localExists := fun d : G.Dart =>
    PolygonalArcCollarLocalSideDataExistsWithEndpointLeftCones (A.dartArc d)
      (controlRadii d) (middleSegments d) (forbiddenMargins d)
      (compatibleTubes d) (sourceRadius d) (targetRadius d)
      (sourceAperture d) (targetAperture d) (hsourceRadius_pos d)
      (htargetRadius_pos d) (hsourceAperture_pos d) (htargetAperture_pos d)
      (by
        simpa using (hcontrolSpec d).1)
      (by
        simpa using (hcontrolSpec d).2.1)
      (by
        simpa using (htubeSpec d).1)
      (by
        simpa using (htubeSpec d).2.1)
      (by
        simpa using (hcontrolSpec d).2.2.1)
      (by
        simpa using (hcontrolSpec d).2.2.2)
  let vertexLocalPieces :
      ∀ d : G.Dart,
        PolygonalArcCollarVertexLocalPieceData (A.dartArc d) (controlRadii d)
          (middleSegments d) (forbiddenMargins d)
          (compatibleTubes d).orientedTubes.toPolygonalArcCollarSeparatedTubeData :=
    fun d => Classical.choose (localExists d)
  let localSideData :
      ∀ d : G.Dart,
        PolygonalArcCollarLocalSideData (A.dartArc d) (controlRadii d)
          (middleSegments d) (forbiddenMargins d)
          (compatibleTubes d).orientedTubes (vertexLocalPieces d) :=
    fun d => Classical.choose (Classical.choose_spec (localExists d))
  have hlocalSpec :
      ∀ d : G.Dart,
        let γ := A.dartArc d
        let hsource : 0 < γ.vertices.length := by
          have hlen := γ.length_ge_two
          omega
        let itarget : ℕ := γ.vertices.length - 1
        let htarget : itarget < γ.vertices.length := by
          have hlen := γ.length_ge_two
          dsimp [itarget]
          omega
        γ.source ∉ (localSideData d).vertexCollar ⟨0, hsource⟩ ∧
          γ.target ∉ (localSideData d).vertexCollar ⟨itarget, htarget⟩ ∧
            ((localSideData d).vertexCollar ⟨0, hsource⟩ \ γ.relativeInterior ⊆
              PolygonalArcInitialEndpointCone γ (sourceRadius d)
                (sourceAperture d)) ∧
              ((localSideData d).vertexCollar ⟨itarget, htarget⟩ \
                  γ.relativeInterior ⊆
                PolygonalArcTerminalEndpointCone γ (targetRadius d)
                  (targetAperture d)) ∧
                (∀ i : Fin γ.vertices.length, i.1 ≠ 0 →
                  Disjoint ((localSideData d).vertexCollar i)
                    (Metric.ball γ.source (sourceRadius d))) ∧
                  (∀ i : Fin γ.vertices.length,
                    i.1 + 1 ≠ γ.vertices.length →
                      Disjoint ((localSideData d).vertexCollar i)
                        (Metric.ball γ.target (targetRadius d))) ∧
                    (localSideData d).leftSidePiece ⟨0, hsource⟩ ⊆
                      PolygonalArcInitialEndpointLeftCone γ (sourceRadius d)
                        (sourceAperture d) ∧
                      (localSideData d).leftSidePiece ⟨itarget, htarget⟩ ⊆
                        PolygonalArcTerminalEndpointLeftCone γ (targetRadius d)
                          (targetAperture d) ∧
                        (localSideData d).rightSidePiece ⟨0, hsource⟩ ⊆
                          PolygonalArcTerminalEndpointLeftCone
                            (PolygonalArcReverse γ) (sourceRadius d)
                            (sourceAperture d) ∧
                          (localSideData d).rightSidePiece
                              ⟨itarget, htarget⟩ ⊆
                            PolygonalArcInitialEndpointLeftCone
                              (PolygonalArcReverse γ) (targetRadius d)
                              (targetAperture d) := by
    intro d
    dsimp [localSideData, vertexLocalPieces, localExists]
    exact Classical.choose_spec (Classical.choose_spec (localExists d))
  rcases PlaneDrawingDartCoherentSideStripsExist G D hD A C with
    ⟨sideStrips, hleftStrip_nonempty, hleftStrip_subset_complement,
      hlocalComplement_subset_sideStrips, hrightStrip_eq_leftStrip_symm,
      hsuccessorSector_meets_leftStrip,
      hsuccessorSector_meets_successor_leftStrip⟩
  refine ⟨
    { sourceRadius := sourceRadius
      targetRadius := targetRadius
      endpointIsolation := hendpointIsolation
      sourceRadius_lt_localDisk := hsourceRadius_lt_localDisk
      targetRadius_lt_localDisk := htargetRadius_lt_localDisk
      sourceAperture := sourceAperture
      targetAperture := targetAperture
      sourceAperture_pos := hsourceAperture_pos
      targetAperture_pos := htargetAperture_pos
      terminalSectorRadius := terminalSectorRadius
      terminalSectorAperture := terminalSectorAperture
      terminalSectorRadius_pos := fun d => (hterminalSpec d).1
      terminalSectorAperture_pos := fun d => (hterminalSpec d).2.1
      terminalSector_subset_successorSector := fun d => (hterminalSpec d).2.2
      successorInitialSectorRadius := successorInitialSectorRadius
      successorInitialSectorAperture := successorInitialSectorAperture
      successorInitialSectorRadius_pos := fun d => (hsuccessorInitialSpec d).1
      successorInitialSectorAperture_pos := fun d =>
        (hsuccessorInitialSpec d).2.1
      successorInitialSector_subset_successorSector := fun d =>
        (hsuccessorInitialSpec d).2.2
      targetRadius_lt_terminalSectorRadius := htargetRadius_lt_terminal
      targetAperture_lt_terminalSectorAperture := htargetAperture_lt_terminal
      successor_sourceRadius_lt_initialSectorRadius := ?_
      successor_sourceAperture_lt_initialSectorAperture := ?_
      eta := eta
      eta_pos := heta_pos
      eta_lt_sourceRadius := heta_lt_source
      eta_lt_targetRadius := heta_lt_target
      awaySeparation := awaySeparation
      awaySeparation_pos := fun d => (hawaySpec d).1
      eta_lt_awaySeparation := heta_lt_away
      awaySeparation_le_dist := fun d => (hawaySpec d).2
      controlRadii := controlRadii
      source_controlRadius_lt := ?_
      target_controlRadius_lt := ?_
      source_controlBall_disjoint := ?_
      target_controlBall_disjoint := ?_
      middleSegments := middleSegments
      forbiddenMargins := forbiddenMargins
      compatibleTubes := compatibleTubes
      initialConeBound_lt_sourceAperture := ?_
      terminalConeBound_lt_targetAperture := ?_
      nonfirst_tube_disjoint_sourceBall := ?_
      nonlast_tube_disjoint_targetBall := ?_
      first_leftHalf_sourceBall_subset_initialCone := ?_
      last_leftHalf_targetBall_subset_terminalCone := ?_
      vertexLocalPieces := vertexLocalPieces
      localSideData := localSideData
      source_leftSidePiece_subset_initialCone := ?_
      target_leftSidePiece_subset_terminalCone := ?_
      sideStrips := sideStrips
      leftStrip_nonempty := hleftStrip_nonempty
      leftStrip_subset_complement := hleftStrip_subset_complement
      localComplement_subset_sideStrips := hlocalComplement_subset_sideStrips
      rightStrip_eq_leftStrip_symm := hrightStrip_eq_leftStrip_symm
      successorSector_meets_leftStrip := hsuccessorSector_meets_leftStrip
      successorSector_meets_successor_leftStrip :=
        hsuccessorSector_meets_successor_leftStrip }⟩
  · intro d
    have h := hsourceRadius_lt_successorInitial (C.star.successor d)
    simpa using h
  · intro d
    have h := hsourceAperture_lt_successorInitial (C.star.successor d)
    simpa using h
  · intro d hsource
    simpa using (hcontrolSpec d).1
  · intro d htarget
    simpa using (hcontrolSpec d).2.1
  · intro d i hi
    exact (hcontrolSpec d).2.2.1 i hi
  · intro d i hi
    exact (hcontrolSpec d).2.2.2 i hi
  · intro d hfirst
    simpa using (htubeSpec d).1
  · intro d hlast
    simpa using (htubeSpec d).2.1
  · intro d j hj hj0
    exact (htubeSpec d).2.2.1 j hj hj0
  · intro d j hj hjlast
    exact (htubeSpec d).2.2.2 j hj (by
      intro h
      exact hjlast (by
        have hlen := (A.dartArc d).length_ge_two
        omega))
  · intro d hfirst
    have hlast : ((A.dartArc d).vertices.length - 2) + 1 <
        (A.dartArc d).vertices.length := by
      have hlen := (A.dartArc d).length_ge_two
      omega
    exact
      (PolygonalArcEndpointLeftHalfTubeSubsetLeftCones (A.dartArc d)
        (controlRadii d) (middleSegments d) (forbiddenMargins d)
        (compatibleTubes d) (sourceRadius d) (targetRadius d)
        (sourceAperture d) (targetAperture d) (hendpointIsolation d)
        (hsourceAperture_pos d) (htargetAperture_pos d) hfirst hlast
        (by simpa using (htubeSpec d).1)
        (by simpa using (htubeSpec d).2.1)).1
  · intro d hlast
    have hfirst : 0 + 1 < (A.dartArc d).vertices.length := by
      have hlen := (A.dartArc d).length_ge_two
      omega
    exact
      (PolygonalArcEndpointLeftHalfTubeSubsetLeftCones (A.dartArc d)
        (controlRadii d) (middleSegments d) (forbiddenMargins d)
        (compatibleTubes d) (sourceRadius d) (targetRadius d)
        (sourceAperture d) (targetAperture d) (hendpointIsolation d)
        (hsourceAperture_pos d) (htargetAperture_pos d) hfirst hlast
        (by simpa using (htubeSpec d).1)
        (by simpa using (htubeSpec d).2.1)).2.1
  · intro d hsource
    rcases hlocalSpec d with
      ⟨_, _, _, _, _, _, hleft_source, _hleft_target, _hright_source,
        _hright_target⟩
    simpa using hleft_source
  · intro d htarget
    rcases hlocalSpec d with
      ⟨_, _, _, _, _, _, _hleft_source, hleft_target, _hright_source,
        _hright_target⟩
    simpa using hleft_target
