import Util.IncidenceGeometry.EndpointSidePrefixAttachment
import Util.IncidenceGeometry.EndpointSidePrefixCoreSimplePath
import Util.IncidenceGeometry.EndpointSidePrefixEventBallSurgery
import Util.IncidenceGeometry.EndpointSidePrefixTerminalAssembly
import Util.IncidenceGeometry.FinitePolygonalSet
import Util.IncidenceGeometry.PolygonalArc
import Util.IncidenceGeometry.PolygonalSideStrips

open Classical
noncomputable section

lemma EndpointSidePrefixConstruction
    (Aarc Barc BplusArc : PolygonalArc)
    (S : PolygonalSideStrips Aarc)
    (SelectedSide : Set (EuclideanSpace ℝ (Fin 2)))
    (Rbeta H Bad StartSector DeltaX Qx
      TerminalSideRegion TerminalBridgeRegion :
        Set (EuclideanSpace ℝ (Fin 2)))
    (terminalGate terminalSideSource quadrantGate :
      EuclideanSpace ℝ (Fin 2))
    (eventRadius : EuclideanSpace ℝ (Fin 2) → ℝ)
    (K : FinitePolygonalSet)
    (XA : Finset (EuclideanSpace ℝ (Fin 2))) :
    K.carrier = H →
      Set.Finite Bad →
        (K.points : Set (EuclideanSpace ℝ (Fin 2))) ⊆ Bad →
      (SelectedSide = S.leftStrip ∨ SelectedSide = S.rightStrip) →
        Aarc.source ∈ closure SelectedSide →
      Aarc.source = Barc.source →
        Aarc.target = Barc.target →
          BplusArc.source = Aarc.target →
            Aarc.source ≠ Aarc.target →
              Aarc.target ≠ BplusArc.target →
                Aarc.source ≠ BplusArc.target →
                  Aarc.carrier ∩ Barc.carrier =
                      ({Aarc.source, Aarc.target} :
                        Set (EuclideanSpace ℝ (Fin 2))) →
                    Aarc.carrier ∩ BplusArc.carrier =
                        ({Aarc.target} : Set (EuclideanSpace ℝ (Fin 2))) →
                      Barc.carrier ∩ BplusArc.carrier =
                          ({Aarc.target} : Set (EuclideanSpace ℝ (Fin 2))) →
                        BplusArc.carrier ∩ H =
                            ({Aarc.target, BplusArc.target} :
                              Set (EuclideanSpace ℝ (Fin 2))) →
                          Rbeta ⊆ H →
                            Disjoint Aarc.carrier Rbeta →
                            BplusArc.target ∈ Rbeta →
                              Rbeta ∩ (Barc.carrier ∪ BplusArc.carrier) =
                                  ({BplusArc.target} :
                                    Set (EuclideanSpace ℝ (Fin 2))) →
                                BplusArc.target ∉ Aarc.carrier →
                                  (∀ p : EuclideanSpace ℝ (Fin 2),
                                    p ∈ XA ↔
                                      p ∈ Aarc.carrier \
                                          ({Aarc.source, Aarc.target} :
                                            Set (EuclideanSpace ℝ (Fin 2))) ∧
                                        p ∈ H) →
                                    (∀ p q : EuclideanSpace ℝ (Fin 2),
                                      p ≠ q →
                                        segment ℝ p q ⊆ Aarc.carrier ∩ H →
                                          False) →
                                      (∀ p : EuclideanSpace ℝ (Fin 2),
                                        p ∈ XA →
                                          p ∉
                                              (K.points :
                                                Set (EuclideanSpace ℝ (Fin 2))) ∧
                                            ∃ j : ℕ,
                                              ∃ hj : j + 1 < Aarc.vertices.length,
                                                p ∈
                                                    openSegment ℝ
                                                      Aarc.vertices[j]
                                                      Aarc.vertices[j + 1] ∧
                                              ∃! s :
                                                EuclideanSpace ℝ (Fin 2) ×
                                                  EuclideanSpace ℝ (Fin 2),
                                                s ∈ K.segments ∧
                                                  p ∈ openSegment ℝ s.1 s.2 ∧
                                                    ¬ ∃ c : ℝ,
                                                      s.2 - s.1 =
                                                        c •
                                                          (Aarc.vertices[j + 1] -
                                                            Aarc.vertices[j])) →
                                        (∀ p : EuclideanSpace ℝ (Fin 2),
                                          p ∈ XA →
                                            0 < eventRadius p ∧
                                            Convex ℝ
                                              (SelectedSide ∩
                                                Metric.ball p (eventRadius p)) ∧
                                            ∃ s :
                                              EuclideanSpace ℝ (Fin 2) ×
                                                EuclideanSpace ℝ (Fin 2),
                                                s ∈ K.segments ∧
                                                    p ∈ openSegment ℝ s.1 s.2 ∧
                                                      Metric.ball p (eventRadius p) ∩ H =
                                                        Metric.ball p (eventRadius p) ∩
                                                          segment ℝ s.1 s.2 ∧
                                                        Metric.ball p (eventRadius p) ∩ Rbeta =
                                                          (∅ :
                                                            Set
                                                              (EuclideanSpace ℝ
                                                                (Fin 2)))) →
                                          (∀ p : EuclideanSpace ℝ (Fin 2),
                                            p ∈ XA →
                                              Disjoint
                                                (Metric.closedBall p (eventRadius p))
                                                (closure StartSector)) →
                                          (∀ p q : EuclideanSpace ℝ (Fin 2),
                                            p ∈ XA → q ∈ XA → p ≠ q →
                                              Disjoint
                                                (Metric.closedBall p (eventRadius p))
                                                (Metric.closedBall q (eventRadius q))) →
                                            SelectedSide ∩
                                                (Barc.carrier ∪ BplusArc.carrier ∪
                                                  Rbeta ∪ Bad) =
                                              (∅ : Set (EuclideanSpace ℝ (Fin 2))) →
                                              SelectedSide ∩
                                                  (closure TerminalSideRegion ∪
                                                    closure TerminalBridgeRegion ∪ closure Qx) =
                                                (∅ : Set (EuclideanSpace ℝ (Fin 2))) →
                                              SelectedSide ∩ H ⊆
                                                ⋃ p ∈ (XA : Set (EuclideanSpace ℝ (Fin 2))),
                                                  Metric.ball p (eventRadius p) →
                                          IsOpen StartSector →
                                            Convex ℝ StartSector →
                                              StartSector ⊆ SelectedSide →
                                              Aarc.source ∈ closure StartSector →
                                                Aarc.source ∉ StartSector →
                                                  StartSector ∩
                                                  (Aarc.carrier ∪ Barc.carrier ∪
                                                    BplusArc.carrier ∪ Rbeta ∪
                                                      H ∪ Bad) =
                                                (∅ :
                                                  Set (EuclideanSpace ℝ (Fin 2))) →
                                              Aarc.target ∈ DeltaX →
                                                BplusArc.target ∈ DeltaX →
                                                  BplusArc.carrier ⊆ DeltaX →
                                                    Qx ⊆ DeltaX →
                                                      Convex ℝ Qx →
                                                        IsCompact (closure Qx) →
                                                        Aarc.target ∈ closure Qx →
                                                          (∃ q : EuclideanSpace ℝ (Fin 2),
                                                            q ∈ Qx ∧
                                                              q ≠ BplusArc.target) →
                                                            BplusArc.target ∈ Qx →
                                                              Aarc.target ∉ Qx →
                                                              Qx ∩
                                                                (Aarc.carrier ∪
                                                                  Barc.carrier ∪
                                                                    BplusArc.carrier ∪
                                                                      Rbeta ∪ H) =
                                                              ({BplusArc.target} :
                                                                Set
                                                                  (EuclideanSpace ℝ
                                                                    (Fin 2))) →
                                                                IsOpen TerminalSideRegion →
                                                                  Convex ℝ TerminalSideRegion →
                                                                    IsCompact (closure TerminalSideRegion) →
                                                                      TerminalSideRegion ⊆ DeltaX →
                                                                        (TerminalSideRegion ∪
                                                                            ({terminalGate, terminalSideSource} :
                                                                              Set (EuclideanSpace ℝ (Fin 2)))) ∩
                                                                            ((Aarc.carrier ∪ Barc.carrier ∪
                                                                                BplusArc.carrier ∪ Rbeta ∪ H) ∪ Bad) =
                                                                          (∅ : Set (EuclideanSpace ℝ (Fin 2))) →
                                                                          terminalGate ∈ DeltaX →
                                                                            terminalGate ∈ closure TerminalSideRegion →
                                                                              terminalGate ∉ TerminalSideRegion →
                                                                                terminalGate ∉ Qx →
                                                                                  terminalSideSource ∈ closure TerminalSideRegion →
                                                                                    terminalSideSource ∈ DeltaX →
                                                                                      terminalSideSource ∉ TerminalSideRegion →
                                                                                      terminalGate ≠ terminalSideSource →
                                                                                      segment ℝ terminalGate terminalSideSource ⊆
                                                                                        TerminalSideRegion ∪
                                                                                          ({terminalGate, terminalSideSource} :
                                                                                            Set (EuclideanSpace ℝ (Fin 2))) →
                                                                                        openSegment ℝ terminalGate terminalSideSource ⊆
                                                                                          TerminalSideRegion →
                                                                                          IsOpen TerminalBridgeRegion →
                                                                                            Convex ℝ TerminalBridgeRegion →
                                                                                              IsCompact (closure TerminalBridgeRegion) →
                                                                                                TerminalBridgeRegion ⊆ DeltaX →
                                                                                                  (TerminalBridgeRegion ∪
                                                                                                      ({terminalSideSource, quadrantGate} :
                                                                                                        Set (EuclideanSpace ℝ (Fin 2)))) ∩
                                                                                                      ((Aarc.carrier ∪ Barc.carrier ∪
                                                                                                          BplusArc.carrier ∪ Rbeta ∪ H) ∪ Bad) =
                                                                                                    (∅ : Set (EuclideanSpace ℝ (Fin 2))) →
                                                                                                    terminalSideSource ∈ closure TerminalBridgeRegion →
                                                                                                      terminalSideSource ∉ TerminalBridgeRegion →
                                                                                                        quadrantGate ∈ closure TerminalBridgeRegion →
                                                                                                          quadrantGate ∉ TerminalBridgeRegion →
                                                                                                            terminalSideSource ≠ quadrantGate →
                                                                                                              segment ℝ terminalSideSource quadrantGate ⊆
                                                                                                                TerminalBridgeRegion ∪
                                                                                                                  ({terminalSideSource, quadrantGate} :
                                                                                                                    Set (EuclideanSpace ℝ (Fin 2))) →
                                                                                                                openSegment ℝ terminalSideSource quadrantGate ⊆
                                                                                                                  TerminalBridgeRegion →
                                                                                                                  quadrantGate ∈ Qx →
                                                                                                                    quadrantGate ≠ BplusArc.target →
                                                                                                                      segment ℝ terminalSideSource quadrantGate ∩ Qx =
                                                                                                                        ({quadrantGate} :
                                                                                                                          Set (EuclideanSpace ℝ (Fin 2))) →
                                                                                                                        closure TerminalSideRegion ∩
                                                                                                                            closure TerminalBridgeRegion =
                                                                                                                          ({terminalSideSource} :
                                                                                                                            Set (EuclideanSpace ℝ (Fin 2))) →
                                                                                                                          closure TerminalSideRegion ∩ closure Qx =
                                                                                                                            (∅ : Set (EuclideanSpace ℝ (Fin 2))) →
                                                                                                                            closure TerminalBridgeRegion ∩ closure Qx =
                                                                                                                              ({quadrantGate} :
                                                                                                                                Set (EuclideanSpace ℝ (Fin 2))) →
                                                                                                                              segment ℝ quadrantGate BplusArc.target ⊆ Qx →
                                                                                                                                openSegment ℝ quadrantGate BplusArc.target ∩
                                                                                                                                    ((Aarc.carrier ∪ Barc.carrier ∪
                                                                                                                                        BplusArc.carrier ∪ Rbeta ∪ H) ∪ Bad) =
                                                                                                                                  (∅ : Set (EuclideanSpace ℝ (Fin 2))) →
                                                                  (∃ h : EuclideanSpace ℝ (Fin 2),
                                                                      ∃ Vin : Set (EuclideanSpace ℝ (Fin 2)),
                                                                          ∃ predecessor : PolygonalArc,
                                                                            ∃ approach : PolygonalArc,
                                                                              ∃ lastGate : EuclideanSpace ℝ (Fin 2),
                                                                          predecessor.carrier ⊆ SelectedSide ∩ Vin ∧
                                                                            approach.carrier ⊆ SelectedSide ∩ Vin ∧
                                                                              predecessor.target = lastGate ∧
                                                                                approach.source = lastGate ∧
                                                                                  predecessor.carrier ∩ approach.carrier =
                                                                                    ({lastGate} :
                                                                                      Set (EuclideanSpace ℝ (Fin 2))) ∧
                                                                                    approach.target = h ∧
                                                                                      approach.carrier ∩
                                                                                          segment ℝ h terminalGate =
                                                                                        ({h} :
                                                                                          Set (EuclideanSpace ℝ (Fin 2))) ∧
                                                                                        Disjoint predecessor.carrier
                                                                                          (segment ℝ h
                                                                                            terminalGate) ∧
                                                                          IsOpen Vin ∧
                                                                            Convex ℝ Vin ∧
                                                                              h ∈ Vin ∧
                                                                                h ≠ terminalGate ∧
                                                                                  h ∉
                                                                                      (Aarc.carrier ∪
                                                                                        Barc.carrier ∪
                                                                                          BplusArc.carrier ∪
                                                                                            Rbeta ∪ H ∪ Bad) ∧
                                                                                    Vin ⊆ SelectedSide ∧
                                                                                      Aarc.target ∈ closure Vin ∧
                                                                                        (∃ ε : ℝ, 0 < ε ∧
                                                                                          SelectedSide ∩ Metric.ball Aarc.target ε ⊆ Vin) ∧
                                                                                    Vin ⊆ DeltaX ∧
                                                                                      Vin ∩ Qx =
                                                                                        (∅ : Set (EuclideanSpace ℝ (Fin 2))) ∧
                                                                                        Vin ∩
                                                                                            ((Aarc.carrier ∪
                                                                                                  Barc.carrier ∪
                                                                                                    BplusArc.carrier ∪
                                                                                                      Rbeta ∪ H) ∪
                                                                                              Bad) =
                                                                                          (∅ :
                                                                                            Set
                                                                                              (EuclideanSpace ℝ
                                                                                                (Fin 2))) ∧
                                                                                          terminalGate ∈ closure Vin ∧
                                                                                            terminalGate ∉ Vin ∧
                                                                                              segment ℝ h terminalGate ⊆
                                                                                                Vin ∪
                                                                                                  ({terminalGate} :
                                                                                                    Set
                                                                                                      (EuclideanSpace ℝ
                                                                                                        (Fin 2))) ∧
                                                                                                openSegment ℝ h terminalGate ⊆
                                                                                                  Vin ∧
                                                                                                  segment ℝ h terminalGate ∩
                                                                                                      (TerminalSideRegion ∪
                                                                                                        ({terminalGate} :
                                                                                                          Set
                                                                                                            (EuclideanSpace ℝ
                                                                                                              (Fin 2)))) =
                                                                                                    ({terminalGate} :
                                                                                                      Set
                                                                                                        (EuclideanSpace ℝ
                                                                                                          (Fin 2))) ∧
                                                                                                    closure Vin ∩
                                                                                                        closure TerminalSideRegion =
                                                                                                      ({terminalGate} :
                                                                                                        Set
                                                                                                          (EuclideanSpace ℝ
                                                                                                            (Fin 2))) ∧
                                                                                                      closure Vin ∩
                                                                                                          closure TerminalBridgeRegion =
                                                                                                        (∅ :
                                                                                                          Set
                                                                                                            (EuclideanSpace ℝ
                                                                                                              (Fin 2))) ∧
                                                                                                      Vin ∩ TerminalSideRegion =
                                                                                                        (∅ :
                                                                                                          Set
                                                                                                            (EuclideanSpace ℝ
                                                                                                              (Fin 2))) ∧
                                                                                                        (∀ p : EuclideanSpace ℝ (Fin 2),
                                                                                                          p ∈ XA →
                                                                                                            Disjoint
                                                                                                              (Metric.closedBall p
                                                                                                                (eventRadius p))
                                                                                                              (closure Vin))) →
                                                                ∃ E :
                                                                  EndpointSidePrefixAttachment
                                                                    Aarc Barc BplusArc
                                                                    Rbeta H Bad DeltaX Qx
                                                                    K XA,
                                                                  (E.prefixPiece 0).source =
                                                                      Aarc.source ∧
                                                                    (E.prefixPiece 0).carrier ⊆
                                                                        StartSector ∪
                                                                          ({Aarc.source} :
                                                                            Set
                                                                              (EuclideanSpace ℝ
                                                                                (Fin 2))) ∧
                                                                      (E.prefixPiece 0).relativeInterior ⊆
                                                                        StartSector ∧
                                                                        3 ≤ E.r ∧
                                                                          ∃ h lastGate :
                                                                              EuclideanSpace ℝ (Fin 2),
                                                                            ∃ Vin : Set (EuclideanSpace ℝ (Fin 2)),
                                                                              (E.prefixPiece (E.r - 3)).carrier ⊆
                                                                                  SelectedSide ∩ Vin ∧
                                                                                (E.prefixPiece (E.r - 2)).carrier ⊆
                                                                                    SelectedSide ∩ Vin ∧
                                                                                  (E.prefixPiece (E.r - 3)).target =
                                                                                      lastGate ∧
                                                                                    (E.prefixPiece (E.r - 2)).source =
                                                                                        lastGate ∧
                                                                                      (E.prefixPiece (E.r - 3)).carrier ∩
                                                                                          (E.prefixPiece (E.r - 2)).carrier =
                                                                                        ({lastGate} :
                                                                                          Set
                                                                                            (EuclideanSpace ℝ (Fin 2))) ∧
                                                                                        (E.prefixPiece (E.r - 2)).target = h ∧
                                                                                          (E.prefixPiece (E.r - 1)).source = h ∧
                                                                                            (E.prefixPiece (E.r - 1)).target =
                                                                                                terminalGate ∧
                                                                                              (E.prefixPiece (E.r - 2)).carrier ∩
                                                                                                  (E.prefixPiece (E.r - 1)).carrier =
                                                                                                ({h} :
                                                                                                  Set
                                                                                                    (EuclideanSpace ℝ (Fin 2))) ∧
                                                                                                (E.prefixPiece (E.r - 1)).carrier =
                                                                                                  segment ℝ h
                                                                                                    terminalGate ∧
                                                                                                  Disjoint
                                                                                                    (E.prefixPiece (E.r - 3)).carrier
                                                                                                    (E.prefixPiece (E.r - 1)).carrier ∧
                                                                                                  (E.prefixPiece E.r).source =
                                                                                                      terminalGate ∧
                                                                                                    (E.prefixPiece (E.r - 1)).carrier ∩
                                                                                                        (E.prefixPiece E.r).carrier =
                                                                                                      ({terminalGate} :
                                                                                                        Set
                                                                                                          (EuclideanSpace ℝ (Fin 2))) ∧
                                                                                                      (E.prefixPiece E.r).carrier =
                                                                                                        segment ℝ terminalGate terminalSideSource ∧
                                                                                                        E.terminalSide.carrier =
                                                                                                          segment ℝ terminalSideSource quadrantGate ∧
                                                                                                          E.terminalConnector.carrier =
                                                                                                            segment ℝ quadrantGate BplusArc.target := by
  intro hK hBadFinite hKpoints hSelectedSide hSourceClosure
    hSourceEq hTargetEq hBplusSource hSourceNeTarget hTargetNeBplusTarget
    hSourceNeBplusTarget hAB hABplus hBBplus hBplusH hRbetaH hATail
    hBplusTargetTail hTailOld hBplusTargetNotA hXA hNoCommonSegment
    hCleanEvent hEventBall hSourceEventSeparation hClosedBalls hSideAvoid hSideTerminalAvoid
    hSideH hStartOpen hStartConvex hStartSubset hSourceClStart
    hSourceNotStart hStartAvoid hAtargetDelta hBtargetDelta hBplusDelta
    hQDelta hQConvex hQCompact hAtargetClQ hQNontrivial hBtargetQ
    hAtargetNotQ hQOld hTerminalSideOpen hTerminalSideConvex
    hTerminalSideCompact hTerminalSideDelta hTerminalSideAvoid hGateDelta
    hGateClTerminalSide hGateNotTerminalSide hGateNotQ
    hTerminalSideSourceCl hTerminalSideSourceDelta hTerminalSideSourceNot
    hGateNeTerminalSideSource hTerminalSideSegment hTerminalSideOpenSegment
    hTerminalBridgeOpen hTerminalBridgeConvex hTerminalBridgeCompact
    hTerminalBridgeDelta hTerminalBridgeAvoid hTerminalSideSourceBridgeCl
    hTerminalSideSourceNotBridge hQuadrantBridgeCl hQuadrantNotBridge
    hTerminalSideSourceNeQuadrant hTerminalBridgeSegment
    hTerminalBridgeOpenSegment hQuadrantQ hQuadrantNeTarget
    hTerminalBridgeMeetsQ hTerminalClosuresMeet hTerminalSideClosureQ
    hTerminalBridgeClosureQ hTerminalConnectorSegment
    hTerminalConnectorOpenAvoid hTerminalApproach
  rcases hTerminalApproach with
    ⟨h, Vin, predecessor, approach, lastGate,
      hPredecessorSubset, hApproachSubset, hPredecessorTarget,
      hApproachSource, hPredecessorApproach, hApproachTarget,
      hApproachIncoming, hPredecessorIncoming, hVinOpen, hVinConvex,
      hhVin, hhNeGate, hhAvoid, hVinSide, hAtargetClVin, hVinNear,
      hVinDelta, hVinQ, hVinAvoid, hGateClVin, hGateNotVin,
      hIncomingSegment, hIncomingOpenSegment, hIncomingTerminal,
      hVinTerminalClosure, hVinBridgeClosure, hVinTerminal,
      hVinEventSeparation⟩
  have hSideA : Disjoint SelectedSide Aarc.carrier := by
    rcases hSelectedSide with hleft | hright
    · simpa [hleft] using S.left_disjoint_arc
    · simpa [hright] using S.right_disjoint_arc
  have hSideOpen : IsOpen SelectedSide := by
    rcases hSelectedSide with hleft | hright
    · simpa [hleft] using S.left_open
    · simpa [hright] using S.right_open
  let Forbidden : Set (EuclideanSpace ℝ (Fin 2)) :=
    (Aarc.carrier ∪ Barc.carrier ∪ BplusArc.carrier ∪ Rbeta ∪ Bad) ∪
      (closure TerminalSideRegion ∪ closure TerminalBridgeRegion ∪ closure Qx)
  let TerminalChain : Set (EuclideanSpace ℝ (Fin 2)) :=
    predecessor.carrier ∪ approach.carrier ∪ segment ℝ h terminalGate
  have hSideForbidden : SelectedSide ∩ Forbidden =
      (∅ : Set (EuclideanSpace ℝ (Fin 2))) := by
    ext x
    constructor
    · rintro ⟨hxSide, hxForbidden⟩
      have hxA : x ∉ Aarc.carrier :=
        Set.disjoint_left.1 hSideA hxSide
      have hxOrdinary :
          x ∉ Barc.carrier ∪ BplusArc.carrier ∪ Rbeta ∪ Bad := by
        intro hx
        have : x ∈ SelectedSide ∩
            (Barc.carrier ∪ BplusArc.carrier ∪ Rbeta ∪ Bad) :=
          ⟨hxSide, hx⟩
        rw [hSideAvoid] at this
        exact this
      have hxTerminal :
          x ∉ closure TerminalSideRegion ∪
            closure TerminalBridgeRegion ∪ closure Qx := by
        intro hx
        have : x ∈ SelectedSide ∩
            (closure TerminalSideRegion ∪
              closure TerminalBridgeRegion ∪ closure Qx) := ⟨hxSide, hx⟩
        rw [hSideTerminalAvoid] at this
        exact this
      rcases hxForbidden with hxOld | hxTerm
      · rcases hxOld with hxThroughRbeta | hxBad'
        · rcases hxThroughRbeta with hxThroughBplus | hxRbeta'
          · rcases hxThroughBplus with hxAB | hxBplus'
            · rcases hxAB with hxA' | hxB'
              · exact (hxA hxA').elim
              · exact (hxOrdinary (by simp [hxB'])).elim
            · exact (hxOrdinary (by simp [hxBplus'])).elim
          · exact (hxOrdinary (by simp [hxRbeta'])).elim
        · exact (hxOrdinary (by simp [hxBad'])).elim
      · exact (hxTerminal hxTerm).elim
    · intro hx
      exact hx.elim
  have hPredecessorSide : predecessor.carrier ⊆ SelectedSide :=
    fun _ hx => (hPredecessorSubset hx).1
  have hApproachSide : approach.carrier ⊆ SelectedSide :=
    fun _ hx => (hApproachSubset hx).1
  have hIncomingSide : openSegment ℝ h terminalGate ⊆ SelectedSide :=
    fun _ hx => hVinSide (hIncomingOpenSegment hx)
  rcases EndpointSidePrefixCoreSimplePath
      Aarc predecessor approach S SelectedSide StartSector Forbidden
      h terminalGate lastGate hSelectedSide hStartOpen hStartConvex
      hStartSubset hSourceClStart hSourceNotStart hPredecessorSide
      hApproachSide hPredecessorTarget hApproachSource
      hPredecessorApproach hApproachTarget hApproachIncoming
      hPredecessorIncoming hhNeGate hIncomingSide hSideForbidden with
    ⟨P0, hP0Source, hP0Target, hP0Carrier, hP0Interior,
      hP0Forbidden, hP0FiniteTerminal, hP0Nodup, hP0Segments,
      hP0VerticesAvoid, hP0First⟩
  rcases hP0First with
    ⟨hP0FirstBound, hP0FirstCarrier, hP0FirstOpen⟩
  have hSideRbetaBad : SelectedSide ∩ (Rbeta ∪ Bad) =
      (∅ : Set (EuclideanSpace ℝ (Fin 2))) := by
    ext x
    constructor
    · rintro ⟨hxSide, hx⟩
      have hx' : x ∈ SelectedSide ∩
          (Barc.carrier ∪ BplusArc.carrier ∪ Rbeta ∪ Bad) :=
        ⟨hxSide, by rcases hx with hx | hx <;> simp [hx]⟩
      rw [hSideAvoid] at hx'
      exact hx'
    · intro hx
      exact hx.elim
  have arcSourceMemCarrier : ∀ Γ : PolygonalArc, Γ.source ∈ Γ.carrier := by
    intro Γ
    rw [Γ.carrier_eq]
    have hseg : 0 + 1 < Γ.vertices.length := by
      have hlen := Γ.length_ge_two
      omega
    refine ⟨0, hseg, ?_⟩
    have hzero : 0 < Γ.vertices.length := by omega
    have hsource : Γ.vertices[0]'hzero = Γ.source := by
      have hhead := Γ.source_eq_head
      rw [List.head?_eq_getElem?] at hhead
      rw [List.getElem?_eq_getElem hzero] at hhead
      exact Option.some.inj hhead
    rw [← hsource]
    exact left_mem_segment ℝ (Γ.vertices[0]'hzero) (Γ.vertices[1]'hseg)
  have hStartH : StartSector ∩ H =
      (∅ : Set (EuclideanSpace ℝ (Fin 2))) := by
    ext x
    constructor
    · rintro ⟨hxStart, hxH⟩
      have hxOld : x ∈
          Aarc.carrier ∪ Barc.carrier ∪ BplusArc.carrier ∪
            Rbeta ∪ H ∪ Bad := by
        simp [hxH]
      have hx : x ∈ StartSector ∩
          (Aarc.carrier ∪ Barc.carrier ∪ BplusArc.carrier ∪
            Rbeta ∪ H ∪ Bad) := ⟨hxStart, hxOld⟩
      rw [hStartAvoid] at hx
      exact hx
    · intro hx
      exact hx.elim
  let EndpointControl : Set (EuclideanSpace ℝ (Fin 2)) :=
    closure StartSector ∪ closure Vin
  have hP0SourceControl : P0.source ∈ EndpointControl := by
    rw [hP0Source]
    exact Or.inl hSourceClStart
  have hP0TargetControl : P0.target ∈ EndpointControl := by
    rw [hP0Target]
    exact Or.inr (subset_closure ((hPredecessorSubset
      (arcSourceMemCarrier predecessor)).2))
  have hP0FirstControl :
      segment ℝ P0.vertices[0] P0.vertices[1] ⊆ EndpointControl := by
    intro z hz
    rcases hP0FirstCarrier hz with hzStart | hzSource
    · exact Or.inl (subset_closure hzStart)
    · have hzEqA : z = Aarc.source := by simpa using hzSource
      have hzEq : z = P0.source := hzEqA.trans hP0Source.symm
      simpa [hzEq] using hP0SourceControl
  have hTerminalChainControl :
      predecessor.carrier ∪ approach.carrier ∪ segment ℝ h terminalGate ⊆
        EndpointControl := by
    intro z hz
    rcases hz with hz | hz
    · rcases hz with hzPredecessor | hzApproach
      · exact Or.inr (subset_closure ((hPredecessorSubset hzPredecessor).2))
      · exact Or.inr (subset_closure ((hApproachSubset hzApproach).2))
    · rcases hIncomingSegment hz with hzVin | hzGate
      · exact Or.inr (subset_closure hzVin)
      · have hzEq : z = terminalGate := by simpa using hzGate
        rw [hzEq]
        change terminalGate ∈ closure StartSector ∪ closure Vin
        exact Or.inr hGateClVin
  have hEventControlSeparation :
      ∀ p : EuclideanSpace ℝ (Fin 2),
        p ∈ XA →
          Disjoint (Metric.closedBall p (eventRadius p)) EndpointControl := by
    intro p hp
    rw [Set.disjoint_left]
    intro z hzBall hzControl
    rcases hzControl with hzStart | hzVin
    · exact (Set.disjoint_left.1 (hSourceEventSeparation p hp) hzBall hzStart)
    · exact (Set.disjoint_left.1 (hVinEventSeparation p hp) hzBall hzVin)
  rcases EndpointSidePrefixEventBallSurgery
      P0 predecessor approach SelectedSide H Rbeta Bad Forbidden StartSector
      EndpointControl
      h terminalGate K XA eventRadius hSideOpen
      (by simpa [hP0Source] using hP0Carrier)
      hP0Interior hP0Forbidden hSideForbidden hK hhNeGate
      (by simpa [TerminalChain] using hP0FiniteTerminal)
      hP0SourceControl hP0TargetControl
      ⟨hP0FirstBound, by simpa [hP0Source] using hP0FirstCarrier,
        hP0FirstOpen, hP0FirstControl⟩ hTerminalChainControl hStartH hKpoints
      hSideRbetaBad hSideH hEventBall hEventControlSeparation hClosedBalls with
    ⟨Pclean, xClean, charge, hPcleanSource, hPcleanTarget, hPcleanCarrier,
      hPcleanInterior, hPcleanForbidden, hPcleanFiniteTerminal,
      hPcleanFirst, hPcleanNodup, hPcleanSegments, hPcleanVerticesAvoid,
      hxClean, hChargeMem, hChargeInjective, hxCleanLocal,
      hOutsideEventBalls⟩
  have hPcleanOldAvoid :
      Pclean.relativeInterior ∩
          (Aarc.carrier ∪ Barc.carrier ∪ BplusArc.carrier ∪
            Rbeta ∪ Bad) =
        (∅ : Set (EuclideanSpace ℝ (Fin 2))) := by
    ext x
    constructor
    · rintro ⟨hxInterior, hxOld⟩
      have hxForbidden : x ∈ Pclean.relativeInterior ∩ Forbidden :=
        ⟨hxInterior, Or.inl hxOld⟩
      rw [hPcleanForbidden] at hxForbidden
      exact hxForbidden
    · intro hx
      exact hx.elim
  apply EndpointSidePrefixTerminalAssembly
    Aarc Barc BplusArc Pclean predecessor approach SelectedSide Rbeta H Bad
    StartSector DeltaX Qx TerminalSideRegion TerminalBridgeRegion Vin
    terminalGate terminalSideSource quadrantGate h lastGate K XA xClean charge
  · exact hK
  · exact hATail
  · intro hSourceSide
    exact Set.disjoint_left.1 hSideA hSourceSide (arcSourceMemCarrier Aarc)
  · exact hSourceNeBplusTarget
  · intro hGateSide
    have : terminalGate ∈ SelectedSide ∩
        (closure TerminalSideRegion ∪
          closure TerminalBridgeRegion ∪ closure Qx) :=
      ⟨hGateSide, by simp [hGateClTerminalSide]⟩
    rw [hSideTerminalAvoid] at this
    exact this
  · exact hSideTerminalAvoid
  · exact hTerminalSideDelta
  · exact hTerminalBridgeDelta
  · exact hQDelta
  · exact hPcleanSource.trans hP0Source
  · exact hPcleanTarget.trans hP0Target
  · simpa [hPcleanSource, hP0Source] using hPcleanCarrier
  · exact hPcleanOldAvoid
  · simpa [TerminalChain] using hPcleanFiniteTerminal
  · simpa [hPcleanSource, hP0Source] using hPcleanFirst
  · exact hxClean
  · intro z hz
    exact (hChargeMem z hz).1
  · exact hChargeInjective
  · exact hxCleanLocal
  · exact hPredecessorSubset
  · exact hApproachSubset
  · exact hPredecessorTarget
  · exact hApproachSource
  · exact hPredecessorApproach
  · exact hApproachTarget
  · exact hApproachIncoming
  · exact hPredecessorIncoming
  · exact hhVin
  · exact hhNeGate
  · exact hhAvoid
  · exact hVinSide
  · exact hVinDelta
  · exact hVinQ
  · exact hVinAvoid
  · exact hGateClVin
  · exact hGateNotVin
  · exact hIncomingSegment
  · exact hIncomingOpenSegment
  · exact hIncomingTerminal
  · exact hVinTerminalClosure
  · exact hVinBridgeClosure
  · exact hGateDelta
  · exact hGateNotQ
  · exact hTerminalSideSourceDelta
  · exact hGateNeTerminalSideSource
  · exact hTerminalSideSegment
  · exact hTerminalSideOpenSegment
  · exact hTerminalSideAvoid
  · exact hTerminalSideSourceNeQuadrant
  · exact hTerminalBridgeSegment
  · exact hTerminalBridgeOpenSegment
  · exact hTerminalBridgeAvoid
  · exact hQuadrantQ
  · exact hQuadrantNeTarget
  · exact hTerminalBridgeMeetsQ
  · exact hTerminalClosuresMeet
  · exact hTerminalSideClosureQ
  · exact hTerminalBridgeClosureQ
  · exact hTerminalConnectorSegment
  · exact hTerminalConnectorOpenAvoid
