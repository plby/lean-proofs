import ErdosProblems.Erdos733.ST.BigonRerouteSpliceCount
import ErdosProblems.Erdos733.ST.BigonRerouteContactOldEdgeOwner
import ErdosProblems.Erdos733.ST.BigonRerouteFinitePresentationLocalBranch
import ErdosProblems.Erdos733.ST.BigonReroutePrefixAssembly
import ErdosProblems.Erdos733.ST.BigonRerouteBetaSpliceAssembly
import ErdosProblems.Erdos733.ST.BigonReroutePrefixContactClassification
import ErdosProblems.Erdos733.ST.BigonRerouteNewEdgeClassification
import ErdosProblems.Erdos733.ST.FiniteLocalizedPolygonalEdgeAssignmentCertification
import ErdosProblems.Erdos733.ST.EndpointSidePrefixConstruction
import ErdosProblems.Erdos733.ST.FinitePolygonalSet
import ErdosProblems.Erdos733.ST.OrdinaryPolygonalDrawing
import ErdosProblems.Erdos733.ST.PolygonalArc
import ErdosProblems.Erdos733.ST.PolygonalArcFromEndpointGluedPieces
import ErdosProblems.Erdos733.ST.PolygonalSideStrips

open Classical
noncomputable section

-- [TABLET NODE: BigonReroute]
lemma BigonReroute {V : Type*} [Fintype V] (G : SimpleGraph V)
    [Fintype G.edgeSet] (D : OrdinaryPolygonalDrawing G)
    (alpha beta : G.edgeFinset) (u : V)
    (x y : EuclideanSpace ℝ (Fin 2))
    (A B Bplus Rbeta H Bad DeltaX Qx
      TerminalSideRegion TerminalBridgeRegion :
        Set (EuclideanSpace ℝ (Fin 2)))
    (terminalGate terminalSideSource quadrantGate :
      EuclideanSpace ℝ (Fin 2))
    (eventRadius : EuclideanSpace ℝ (Fin 2) → ℝ)
    (Aarc : PolygonalArc)
    (S : PolygonalSideStrips Aarc)
    (SelectedSide : Set (EuclideanSpace ℝ (Fin 2)))
    (XA XB : Finset (EuclideanSpace ℝ (Fin 2))) :
    alpha ≠ beta →
      u ∈ alpha.1 →
        u ∈ beta.1 →
          x ∈ D.crossingSet →
            x ∈ (D.edgeArc alpha).relativeInterior →
              x ∈ (D.edgeArc beta).relativeInterior →
                y ∈ (D.edgeArc beta).relativeInterior →
                  y ≠ x →
                  A ⊆ (D.edgeArc alpha).carrier →
                    B ⊆ (D.edgeArc beta).carrier →
                      Bplus ⊆ (D.edgeArc beta).carrier →
                        Rbeta =
                            (D.edgeArc beta).carrier \
                              ((B ∪ Bplus) \
                                ({y} : Set (EuclideanSpace ℝ (Fin 2)))) →
                          H =
                              (⋃ edge : G.edgeFinset,
                                  if edge = alpha then
                                    (D.edgeArc edge).carrier \
                                      (A \
                                        ({D.vertexPlacement u, x} :
                                          Set (EuclideanSpace ℝ (Fin 2))))
                                  else if edge = beta then
                                    (D.edgeArc edge).carrier \
                                      ((B \
                                          ({D.vertexPlacement u, x} :
                                            Set (EuclideanSpace ℝ (Fin 2)))) ∪
                                        (Bplus \
                                          ({x, y} :
                                            Set (EuclideanSpace ℝ (Fin 2)))))
                                  else
                                    (D.edgeArc edge).carrier) ∪
                                {p : EuclideanSpace ℝ (Fin 2) |
                                  ∃ v : V, v ≠ u ∧ p = D.vertexPlacement v} →
                            (Tail : BigonRerouteOrderedBetaTailData
                              G D beta u y B Bplus Rbeta H) →
                            Aarc.carrier = A →
                              Disjoint Aarc.carrier Rbeta →
                                Aarc.source = D.vertexPlacement u →
                                Aarc.target = x →
                                  (SelectedSide = S.leftStrip ∨
                                    SelectedSide = S.rightStrip) →
                                    D.vertexPlacement u ∈ closure SelectedSide →
                              (∃ StartSector : Set (EuclideanSpace ℝ (Fin 2)),
                                IsOpen StartSector ∧
                                  Convex ℝ StartSector ∧
                                    StartSector ⊆ SelectedSide ∧
                                      D.vertexPlacement u ∈ closure StartSector ∧
                                        D.vertexPlacement u ∉ StartSector ∧
                                          StartSector ∩
                                              ((A ∪ B ∪ Bplus ∪ Rbeta ∪ H) ∪ Bad) =
                                            (∅ : Set (EuclideanSpace ℝ (Fin 2))) ∧
                                          (∀ p : EuclideanSpace ℝ (Fin 2),
                                            p ∈ XA →
                                              Disjoint
                                                (Metric.closedBall p (eventRadius p))
                                                (closure StartSector))) →
                              (∃ Barc : PolygonalArc,
                                Barc.carrier = B ∧
                                  Barc.source = D.vertexPlacement u ∧ Barc.target = x) →
                                (∃ BplusArc : PolygonalArc,
                                  BplusArc.carrier = Bplus ∧
                                    BplusArc.source = x ∧ BplusArc.target = y) →
                                  D.vertexPlacement u ∈ A →
                                    x ∈ A →
                                      D.vertexPlacement u ∈ B →
                                        x ∈ B →
                                          x ∈ Bplus →
                                            y ∈ Bplus →
                                              A ∩ B =
                                                ({D.vertexPlacement u, x} :
                                                  Set (EuclideanSpace ℝ (Fin 2))) →
                                                B ∩ Bplus =
                                                  ({x} :
                                                    Set (EuclideanSpace ℝ (Fin 2))) →
                                                  Bplus \ ({x} :
                                                    Set (EuclideanSpace ℝ (Fin 2))) ⊆
                                                      (D.edgeArc beta).relativeInterior →
                                                    (∀ p, p ∈ Bplus → p ∈ D.crossingSet → p = x) →
                                                      (∀ v : V,
                                                        D.vertexPlacement v ∈ Bplus → False) →
                                                        Set.Finite Bad →
                                                        (∃ K : FinitePolygonalSet, K.carrier = H) →
                                                          (∀ v : V,
                                                            v ≠ u → D.vertexPlacement v ∈ H) →
                                                          (∀ p : EuclideanSpace ℝ (Fin 2),
                                                              p ∈ XA ↔
                                                                p ∈ A \
                                                                  ({D.vertexPlacement u, x} :
                                                                    Set (EuclideanSpace ℝ (Fin 2))) ∧
                                                                  p ∈ H) →
                                                              (∃ Aclean : PolygonalArc,
                                                                ∃ Kclean : FinitePolygonalSet,
                                                                  Aclean = Aarc ∧
                                                                    Aclean.carrier = A ∧
                                                                    Aclean.source = D.vertexPlacement u ∧
                                                                      Aclean.target = x ∧
                                                                        Kclean.carrier = H ∧
                                                                          (∀ v : V,
                                                                            v ≠ u →
                                                                              D.vertexPlacement v ∈
                                                                                (Kclean.points :
                                                                                  Set
                                                                                    (EuclideanSpace ℝ
                                                                                      (Fin 2)))) ∧
                                                                          (Kclean.points :
                                                                              Set (EuclideanSpace ℝ (Fin 2))) ⊆ Bad ∧
                                                                          (∀ p : EuclideanSpace ℝ (Fin 2),
                                                                            p ∈ XA →
                                                                              p ∉
                                                                                  (Kclean.points :
                                                                                    Set (EuclideanSpace ℝ (Fin 2))) ∧
                                                                                ∃ j : ℕ,
                                                                                  ∃ hj : j + 1 < Aclean.vertices.length,
                                                                                    p ∈
                                                                                        openSegment ℝ
                                                                                          Aclean.vertices[j]
                                                                                          Aclean.vertices[j + 1] ∧
                                                                                      ∃! s :
                                                                                        EuclideanSpace ℝ (Fin 2) ×
                                                                                          EuclideanSpace ℝ (Fin 2),
                                                                                        s ∈ Kclean.segments ∧
                                                                                          p ∈ openSegment ℝ s.1 s.2 ∧
                                                                                            ¬ ∃ c : ℝ,
                                                                                              s.2 - s.1 =
                                                                                                c •
                                                                                                  (Aclean.vertices[j + 1] -
                                                                                                    Aclean.vertices[j])) ∧
                                                                            (∀ p : EuclideanSpace ℝ (Fin 2),
                                                                              p ∈ XA →
                                                                                0 < eventRadius p ∧
                                                                                Convex ℝ
                                                                                  (SelectedSide ∩
                                                                                    Metric.ball p (eventRadius p)) ∧
                                                                                ∃ s :
                                                                                  EuclideanSpace ℝ (Fin 2) ×
                                                                                    EuclideanSpace ℝ (Fin 2),
                                                                                    s ∈ Kclean.segments ∧
                                                                                        p ∈ openSegment ℝ s.1 s.2 ∧
                                                                                          Metric.ball p (eventRadius p) ∩ H =
                                                                                            Metric.ball p (eventRadius p) ∩
                                                                                              segment ℝ s.1 s.2 ∧
                                                                                            Metric.ball p (eventRadius p) ∩ Rbeta =
                                                                                              (∅ :
                                                                                                Set
                                                                                                  (EuclideanSpace ℝ
                                                                                                    (Fin 2))))) →
                                                              (∀ p q : EuclideanSpace ℝ (Fin 2),
                                                                p ∈ XA → q ∈ XA → p ≠ q →
                                                                  Disjoint
                                                                    (Metric.closedBall p (eventRadius p))
                                                                    (Metric.closedBall q (eventRadius q))) →
                                                                SelectedSide ∩ (B ∪ Bplus ∪ Rbeta ∪ Bad) =
                                                                  (∅ : Set (EuclideanSpace ℝ (Fin 2))) →
                                                                  SelectedSide ∩
                                                                      (closure TerminalSideRegion ∪
                                                                        closure TerminalBridgeRegion ∪ closure Qx) =
                                                                    (∅ : Set (EuclideanSpace ℝ (Fin 2))) →
                                                                  SelectedSide ∩ H ⊆
                                                                    ⋃ p ∈ (XA : Set (EuclideanSpace ℝ (Fin 2))),
                                                                      Metric.ball p (eventRadius p) →
                                                              x ∈ DeltaX →
                                                                  y ∈ DeltaX →
                                                                    Bplus ⊆ DeltaX →
                                                                      Qx ⊆ DeltaX →
                                                                        Convex ℝ Qx →
                                                                          IsCompact (closure Qx) →
                                                                          x ∈ closure Qx →
                                                                            (∃ q : EuclideanSpace ℝ (Fin 2),
                                                                              q ∈ Qx ∧ q ≠ y) →
                                                                              y ∈ Qx →
                                                                                x ∉ Qx →
                                                                                  Qx ∩
                                                                                  (A ∪ B ∪ Bplus ∪ Rbeta ∪ H) =
                                                                                ({y} :
                                                                                  Set (EuclideanSpace ℝ (Fin 2))) →
                                                                                  IsOpen TerminalSideRegion →
                                                                                    Convex ℝ TerminalSideRegion →
                                                                                      IsCompact (closure TerminalSideRegion) →
                                                                                        TerminalSideRegion ⊆ DeltaX →
                                                                                          (TerminalSideRegion ∪
                                                                                              ({terminalGate, terminalSideSource} :
                                                                                                Set (EuclideanSpace ℝ (Fin 2)))) ∩
                                                                                              ((A ∪ B ∪ Bplus ∪ Rbeta ∪ H) ∪ Bad) =
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
                                                                                                                        ((A ∪ B ∪ Bplus ∪ Rbeta ∪ H) ∪ Bad) =
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
                                                                                                                                      quadrantGate ≠ y →
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
                                                                                                                                                segment ℝ quadrantGate y ⊆ Qx →
                                                                                                                                                  openSegment ℝ quadrantGate y ∩
                                                                                                                                                      ((A ∪ B ∪ Bplus ∪ Rbeta ∪ H) ∪ Bad) =
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
                                                                                                        (A ∪ B ∪ Bplus ∪ Rbeta ∪ H ∪ Bad) ∧
                                                                                                      Vin ⊆ SelectedSide ∧
                                                                                                        x ∈ closure Vin ∧
                                                                                                          (∃ ε : ℝ, 0 < ε ∧
                                                                                                            SelectedSide ∩ Metric.ball x ε ⊆ Vin) ∧
                                                                                                      Vin ⊆ DeltaX ∧
                                                                                                        Vin ∩ Qx =
                                                                                                          (∅ :
                                                                                                            Set
                                                                                                              (EuclideanSpace ℝ
                                                                                                                (Fin 2))) ∧
                                                                                                          Vin ∩
                                                                                                              ((A ∪ B ∪ Bplus ∪ Rbeta ∪ H) ∪ Bad) =
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
                                                              (∀ p : EuclideanSpace ℝ (Fin 2),
                                                                p ∈ XB ↔
                                                                  p ∈ B \
                                                                    ({D.vertexPlacement u, x} :
                                                                      Set (EuclideanSpace ℝ (Fin 2))) ∧
                                                                    p ∈ H) →
                                                                ∃ B' : PolygonalArc,
                                                                ∃ D' : OrdinaryPolygonalDrawing G,
                                                                  D'.vertexPlacement =
                                                                      D.vertexPlacement ∧
                                                                    (∀ edge : G.edgeFinset,
                                                                      edge ≠ beta →
                                                                        D'.edgeArc edge =
                                                                          D.edgeArc edge) ∧
                                                                    B'.carrier ⊆
                                                                        (D'.edgeArc beta).carrier ∧
                                                                      B'.source =
                                                                          D.vertexPlacement u ∧
                                                                        B'.target = y ∧
                                                                          B'.carrier ∩ A =
                                                                            ({D.vertexPlacement u} :
                                                                              Set (EuclideanSpace ℝ (Fin 2))) ∧
                                                                            B'.carrier ∩ (B ∪ Bplus) =
                                                                              ({D.vertexPlacement u, y} :
                                                                                Set (EuclideanSpace ℝ (Fin 2))) ∧
                                                                              B'.carrier ∩ Rbeta =
                                                                                ({y} :
                                                                                  Set (EuclideanSpace ℝ (Fin 2))) ∧
                                                                                (∀ v : V, v ≠ u →
                                                                                  D.vertexPlacement v ∉
                                                                                    B'.carrier) ∧
                                                                                  D'.crossingSet.card +
                                                                                      XB.card + 1 ≤
                                                                                    D.crossingSet.card +
                                                                                      XA.card := by
-- BODY
  intro hAlphaBeta huAlpha huBeta hxCross hxAlpha hxBeta hyBeta hyx
    hAsub hBsub hBplusSub hRbeta hH Tail hAcarrier hARbeta hAsource hAtarget
    hSelected huSelected hStartExists hBarcExists hBplusArcExists huA hxA huB
    hxB hxBplus hyBplus hAB hBBplus hBplusRel hBplusCross hBplusNoVertex
    hBadFinite hKExists hVerticesH hXA hCleanExists hEventBallsDisjoint
    hSelectedAvoid hSelectedTerminal hSelectedH hxDelta hyDelta hBplusDelta
    hQsubset hQconvex hQcompact hxQclosure hQnontrivial hyQ hxnotQ hQinter
    hTermOpen hTermConvex hTermCompact hTermSubset hTermAvoid hGateDelta
    hGateClosure hGateNotTerm hGateNotQ hSideSourceClosure hSideSourceDelta
    hSideSourceNotTerm hGateNeSide hGateSideSeg hGateSideOpen hBridgeOpen
    hBridgeConvex hBridgeCompact hBridgeSubset hBridgeAvoid
    hSideSourceBridgeClosure hSideSourceNotBridge hQuadrantBridgeClosure
    hQuadrantNotBridge hSideNeQuadrant hSideQuadrantSeg hSideQuadrantOpen
    hQuadrantQ hQuadrantNeY hSideQuadrantInterQ hClosTermBridge hClosTermQ
    hClosBridgeQ hQuadrantYSeg hQuadrantYOpenAvoid hApproachExists hXB
  rcases hStartExists with
    ⟨StartSector, hStartOpen, hStartConvex, hStartSubset, huStartClosure,
      huNotStart, hStartAvoid, hEventStartDisjoint⟩
  rcases hBarcExists with ⟨Barc, hBarcCarrier, hBarcSource, hBarcTarget⟩
  rcases hBplusArcExists with
    ⟨BplusArc, hBplusArcCarrier, hBplusArcSource, hBplusArcTarget⟩
  rcases hCleanExists with
    ⟨Aclean, Kclean, hAclean, hAcleanCarrier, hAcleanSource,
      hAcleanTarget, hKclean, hVerticesClean, hCleanPointsBad,
      hCleanContacts, hCleanBalls⟩
  subst Aclean
  have arc_source_ne_target : ∀ Q : PolygonalArc, Q.source ≠ Q.target := by
    intro Q heq
    have hlen := Q.length_ge_two
    have hzero : Q.vertices[0] = Q.source := by
      have hhead := Q.source_eq_head
      rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at hhead
      exact Option.some.inj hhead
    have hlast : Q.vertices[Q.vertices.length - 1] = Q.target := by
      have ht := Q.target_eq_last
      rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at ht
      exact Option.some.inj ht
    have hidx : 0 = Q.vertices.length - 1 :=
      (Q.simple_vertices.getElem_inj_iff).1 (by rw [hzero, hlast, heq])
    omega
  have hu_ne_x : D.vertexPlacement u ≠ x := by
    simpa [hAsource, hAtarget] using arc_source_ne_target Aarc
  have hu_ne_y : D.vertexPlacement u ≠ y := by
    intro huy
    exact D.no_vertex_in_edge_interior u beta (huy ▸ hyBeta)
  have hx_ne_y : x ≠ y := hyx.symm
  have oldCarrierOfNonvertexRelative :
      ∀ (e : G.edgeFinset) (p : EuclideanSpace ℝ (Fin 2)),
        (∀ v : V, p ≠ D.vertexPlacement v) →
          p ∈ (D.edgeArc e).carrier →
            p ∈ (D.edgeArc e).relativeInterior := by
    intro e p hpVertex hpCarrier
    rw [(D.edgeArc e).relativeInterior_eq]
    refine ⟨hpCarrier, ?_⟩
    rcases D.edgeArc_endpoints e with ⟨a, b, _hab, _he, hends⟩
    rcases hends with hends | hends
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨fun hp => hpVertex a (hp.trans hends.1),
        fun hp => hpVertex b (hp.trans hends.2)⟩
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨fun hp => hpVertex b (hp.trans hends.1),
        fun hp => hpVertex a (hp.trans hends.2)⟩
  have hABplus : A ∩ Bplus = ({x} : Set (EuclideanSpace ℝ (Fin 2))) := by
    ext p
    constructor
    · rintro ⟨hpA, hpBplus⟩
      by_cases hpx : p = x
      · simpa [hpx]
      have hpNotVertex : ∀ v : V, p ≠ D.vertexPlacement v := by
        intro v hpv
        exact hBplusNoVertex v (hpv ▸ hpBplus)
      have hpAlphaRel := oldCarrierOfNonvertexRelative alpha p hpNotVertex
        (hAsub hpA)
      have hpBetaRel := hBplusRel ⟨hpBplus, by simpa using hpx⟩
      have hpCross : p ∈ D.crossingSet :=
        (D.crossingSet_spec p).2
          ⟨alpha, beta, hAlphaBeta, hpAlphaRel, hpBetaRel⟩
      exact False.elim (hpx (hBplusCross p hpBplus hpCross))
    · intro hp
      have hpx : p = x := by simpa using hp
      simpa [hpx, hxA, hxBplus]
  have hyRbeta : y ∈ Rbeta := by
    rw [hRbeta]
    refine ⟨by
      rw [(D.edgeArc beta).relativeInterior_eq] at hyBeta
      exact hyBeta.1, ?_⟩
    rintro ⟨_hyOld, hyNotY⟩
    exact hyNotY rfl
  have hRbetaRemoved : Rbeta ∩ (B ∪ Bplus) = ({y} : Set _) := by
    ext p
    constructor
    · rintro ⟨hpR, hpOld⟩
      rw [hRbeta] at hpR
      by_contra hpy
      exact hpR.2 ⟨hpOld, hpy⟩
    · intro hp
      have hpy : p = y := by simpa using hp
      subst p
      exact ⟨hyRbeta, Or.inr hyBplus⟩
  have hyNotA : y ∉ A := by
    intro hyA
    have : y ∈ A ∩ Bplus := ⟨hyA, hyBplus⟩
    rw [hABplus] at this
    exact hyx (by simpa using this)
  have hRbetaH : Rbeta ⊆ H := by
    intro p hpR
    rw [hH]
    left
    apply Set.mem_iUnion.mpr
    refine ⟨beta, ?_⟩
    rw [if_neg hAlphaBeta.symm, if_pos rfl]
    rw [hRbeta] at hpR
    refine ⟨hpR.1, ?_⟩
    rintro (hpB | hpBplus)
    · exact hpR.2 ⟨Or.inl hpB.1, by
        intro hpy
        subst p
        have hyInter : y ∈ B ∩ Bplus := ⟨hpB.1, hyBplus⟩
        rw [hBBplus] at hyInter
        exact hyx (by simpa using hyInter)⟩
    · exact hpR.2 ⟨Or.inr hpBplus.1, by
        intro hpy
        subst p
        exact hpBplus.2 (by simp)⟩
  have hxH : x ∈ H := by
    rw [hH]
    left
    apply Set.mem_iUnion.mpr
    refine ⟨beta, ?_⟩
    rw [if_neg hAlphaBeta.symm, if_pos rfl]
    refine ⟨by
      rw [(D.edgeArc beta).relativeInterior_eq] at hxBeta
      exact hxBeta.1, ?_⟩
    rintro (hxBRemoved | hxBplusRemoved)
    · exact hxBRemoved.2 (by simp)
    · exact hxBplusRemoved.2 (by simp)
  have hyH : y ∈ H := hRbetaH hyRbeta
  have hBplusH : Bplus ∩ H = ({x, y} : Set _) := by
    ext p
    constructor
    · rintro ⟨hpBplus, hpH⟩
      by_cases hpx : p = x
      · simp [hpx]
      have hpBetaRel := hBplusRel ⟨hpBplus, by simpa using hpx⟩
      rw [hH] at hpH
      rcases hpH with hpEdges | hpVertex
      · rcases Set.mem_iUnion.mp hpEdges with ⟨e, hpe⟩
        by_cases heAlpha : e = alpha
        · subst e
          rw [if_pos rfl] at hpe
          have hpAlphaRel : p ∈ (D.edgeArc alpha).relativeInterior := by
            have hpNotVertex : ∀ v : V, p ≠ D.vertexPlacement v := by
              intro v hpv
              exact hBplusNoVertex v (hpv ▸ hpBplus)
            exact oldCarrierOfNonvertexRelative alpha p hpNotVertex hpe.1
          have hpCross : p ∈ D.crossingSet :=
            (D.crossingSet_spec p).2
              ⟨alpha, beta, hAlphaBeta, hpAlphaRel, hpBetaRel⟩
          exact False.elim (hpx (hBplusCross p hpBplus hpCross))
        · rw [if_neg heAlpha] at hpe
          by_cases heBeta : e = beta
          · subst e
            rw [if_pos rfl] at hpe
            have hpNotRemoved := hpe.2
            have hpXY : p = x ∨ p = y := by
              by_contra hpNeither
              apply hpNotRemoved
              right
              exact ⟨hpBplus, by simpa [not_or] using hpNeither⟩
            simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hpXY
          · rw [if_neg heBeta] at hpe
            have hpNotVertex : ∀ v : V, p ≠ D.vertexPlacement v := by
              intro v hpv
              exact hBplusNoVertex v (hpv ▸ hpBplus)
            have hpERel := oldCarrierOfNonvertexRelative e p hpNotVertex hpe
            have hpCross : p ∈ D.crossingSet :=
              (D.crossingSet_spec p).2 ⟨e, beta, heBeta, hpERel, hpBetaRel⟩
            exact False.elim (hpx (hBplusCross p hpBplus hpCross))
      · rcases hpVertex with ⟨v, _hv, hpv⟩
        exact False.elim (hBplusNoVertex v (hpv ▸ hpBplus))
    · intro hp
      rcases hp with hpx | hpy
      · subst p
        exact ⟨hxBplus, hxH⟩
      · subst p
        exact ⟨hyBplus, hyH⟩
  have hNoSegmentAH : ∀ p q : EuclideanSpace ℝ (Fin 2),
      p ≠ q → segment ℝ p q ⊆ Aarc.carrier ∩ H → False := by
    intro p q hpq hsubset
    let forbidden : Finset (EuclideanSpace ℝ (Fin 2)) :=
      XA ∪ {Aarc.source, Aarc.target}
    let f : ℝ → EuclideanSpace ℝ (Fin 2) := AffineMap.lineMap p q
    have hf : Function.Injective f := AffineMap.lineMap_injective ℝ hpq
    let bad : Set ℝ := f ⁻¹' (forbidden : Set (EuclideanSpace ℝ (Fin 2)))
    have hbadFinite : bad.Finite :=
      forbidden.finite_toSet.preimage (fun a _ b _ hab => hf hab)
    have hgood : (Set.Ioo (0 : ℝ) 1 \ bad).Infinite :=
      (Set.Ioo_infinite zero_lt_one).diff hbadFinite
    rcases hgood.nonempty with ⟨t, ht, htbad⟩
    let z := f t
    have hzseg : z ∈ segment ℝ p q :=
      openSegment_subset_segment ℝ p q (lineMap_mem_openSegment ℝ p q ht)
    have hzAH := hsubset hzseg
    have hzNotForbidden : z ∉ forbidden := htbad
    have hzNotEnds : z ∉ ({Aarc.source, Aarc.target} : Set _) := by
      intro hz
      exact hzNotForbidden (by
        change z ∈ XA ∪ {Aarc.source, Aarc.target}
        exact Finset.mem_union_right XA (by simpa using hz))
    have hzXA : z ∈ XA := by
      rw [hXA]
      refine ⟨?_, hzAH.2⟩
      refine ⟨?_, by simpa [hAsource, hAtarget] using hzNotEnds⟩
      rw [← hAcarrier]
      exact hzAH.1
    exact hzNotForbidden (by simp [forbidden, hzXA])
  obtain ⟨E, _hEsource, _hEfirstCarrier, _hEfirstInterior, _hEr,
      _hEterminal⟩ :=
    EndpointSidePrefixConstruction Aarc Barc BplusArc S SelectedSide
      Rbeta H Bad StartSector DeltaX Qx TerminalSideRegion TerminalBridgeRegion
      terminalGate terminalSideSource quadrantGate eventRadius Kclean XA
      hKclean hBadFinite hCleanPointsBad hSelected
      (by simpa [hAsource] using huSelected)
      (by simp [hAsource, hBarcSource])
      (by simp [hAtarget, hBarcTarget])
      (by simp [hAtarget, hBplusArcSource])
      (arc_source_ne_target Aarc)
      (by simpa [hAtarget, hBplusArcTarget] using hx_ne_y)
      (by simpa [hAsource, hBplusArcTarget] using hu_ne_y)
      (by simpa [hAcarrier, hBarcCarrier, hAsource, hAtarget] using hAB)
      (by simpa [hAcarrier, hBplusArcCarrier, hAtarget] using hABplus)
      (by simpa [hBarcCarrier, hBplusArcCarrier, hAtarget] using hBBplus)
      (by simpa [hBplusArcCarrier, hAtarget, hBplusArcTarget] using hBplusH)
      hRbetaH hARbeta
      (by simpa [hBplusArcTarget] using hyRbeta)
      (by simpa [hBarcCarrier, hBplusArcCarrier, hBplusArcTarget] using
        hRbetaRemoved)
      (by simpa [hBplusArcTarget, hAcarrier] using hyNotA)
      (by
        intro p
        simpa [hAcarrier, hAsource, hAtarget] using hXA p)
      hNoSegmentAH hCleanContacts hCleanBalls hEventStartDisjoint
      hEventBallsDisjoint
      (by simpa [hBarcCarrier, hBplusArcCarrier] using hSelectedAvoid)
      hSelectedTerminal hSelectedH hStartOpen hStartConvex hStartSubset
      (by simpa [hAsource] using huStartClosure)
      (by simpa [hAsource] using huNotStart)
      (by simpa [hAcarrier, hBarcCarrier, hBplusArcCarrier] using hStartAvoid)
      (by simpa [hAtarget] using hxDelta)
      (by simpa [hBplusArcTarget] using hyDelta)
      (by simpa [hBplusArcCarrier] using hBplusDelta)
      hQsubset hQconvex hQcompact
      (by simpa [hAtarget] using hxQclosure)
      (by simpa [hBplusArcTarget] using hQnontrivial)
      (by simpa [hBplusArcTarget] using hyQ)
      (by simpa [hAtarget] using hxnotQ)
      (by simpa [hAcarrier, hBarcCarrier, hBplusArcCarrier,
          hBplusArcTarget] using hQinter)
      hTermOpen hTermConvex hTermCompact hTermSubset
      (by simpa [hAcarrier, hBarcCarrier, hBplusArcCarrier] using hTermAvoid)
      hGateDelta hGateClosure hGateNotTerm hGateNotQ hSideSourceClosure
      hSideSourceDelta hSideSourceNotTerm hGateNeSide hGateSideSeg hGateSideOpen
      hBridgeOpen hBridgeConvex hBridgeCompact hBridgeSubset
      (by simpa [hAcarrier, hBarcCarrier, hBplusArcCarrier] using hBridgeAvoid)
      hSideSourceBridgeClosure hSideSourceNotBridge hQuadrantBridgeClosure
      hQuadrantNotBridge hSideNeQuadrant hSideQuadrantSeg hSideQuadrantOpen
      hQuadrantQ (by simpa [hBplusArcTarget] using hQuadrantNeY)
      hSideQuadrantInterQ hClosTermBridge hClosTermQ hClosBridgeQ
      (by simpa [hBplusArcTarget] using hQuadrantYSeg)
      (by
        rw [hBplusArcTarget, hAcarrier, hBarcCarrier, hBplusArcCarrier]
        exact hQuadrantYOpenAvoid)
      (by simpa [hAcarrier, hBarcCarrier, hBplusArcCarrier, hAtarget] using
        hApproachExists)
  obtain ⟨Bprefix, hPrefixSource, hPrefixTarget, hPrefixCarrier,
      hPrefixRelative, hPrefixMeetsA, hPrefixMeetsRemoved,
      hPrefixMeetsTail, hPrefixContacts, hPieceRelative,
      hTerminalSideRelative, hTerminalConnectorRelative, hPieceSegmentLift,
      hTerminalSideSegmentLift, hTerminalConnectorSegmentLift,
      hPrefixSegmentOwner⟩ :=
    BigonReroutePrefixAssembly Aarc Barc BplusArc Rbeta H Bad DeltaX Qx
      Kclean XA E
      (hAsource.trans hBarcSource.symm)
      (by
        rw [hBplusArcTarget, hAcarrier]
        exact hyNotA)
      (by simpa [hBplusArcTarget] using hyRbeta)
  have hPrefixAvoid :
      Bprefix.relativeInterior ∩ (A ∪ B ∪ Bplus ∪ Rbeta) =
        (∅ : Set (EuclideanSpace ℝ (Fin 2))) := by
    ext p
    constructor
    · intro hp
      exfalso
      rcases hp with ⟨hpPrefix, hpOld⟩
      have hpRelative := hpPrefix
      rw [hPrefixRelative] at hpRelative
      rcases hpOld with hpRemoved | hpTail
      · rcases hpRemoved with hpAB | hpBplus
        · rcases hpAB with hpA | hpB
          · have hpMeet : p ∈ Bprefix.carrier ∩ Aarc.carrier :=
              ⟨hpRelative.1, by simpa [hAcarrier] using hpA⟩
            rw [hPrefixMeetsA] at hpMeet
            have hpeq : p = Aarc.source := by simpa using hpMeet
            exact hpRelative.2 (by simp [hpeq])
          · have hpMeet :
                p ∈ Bprefix.carrier ∩ (Barc.carrier ∪ BplusArc.carrier) :=
              ⟨hpRelative.1, Or.inl (by simpa [hBarcCarrier] using hpB)⟩
            rw [hPrefixMeetsRemoved] at hpMeet
            exact hpRelative.2 hpMeet
        · have hpMeet :
              p ∈ Bprefix.carrier ∩ (Barc.carrier ∪ BplusArc.carrier) :=
            ⟨hpRelative.1, Or.inr (by simpa [hBplusArcCarrier] using hpBplus)⟩
          rw [hPrefixMeetsRemoved] at hpMeet
          exact hpRelative.2 hpMeet
      · have hpMeet : p ∈ Bprefix.carrier ∩ Rbeta :=
          ⟨hpRelative.1, hpTail⟩
        rw [hPrefixMeetsTail] at hpMeet
        have hpeq : p = BplusArc.target := by simpa using hpMeet
        exact hpRelative.2 (by simp [hpeq])
    · intro hp
      exact hp.elim
  obtain ⟨hPrefixNoVertex, hPrefixContactClassification⟩ :=
    BigonReroutePrefixContactClassification G D alpha beta u x y
      A B Bplus Rbeta H Bad DeltaX Qx Aarc Barc BplusArc Bprefix Kclean XA E
      huA hAcarrier hBarcCarrier hBplusArcCarrier hRbeta hH hKclean
      hVerticesClean hCleanPointsBad (hPrefixSource.trans hAsource)
      hPrefixContacts hPrefixAvoid
  have hXnewCard : E.xPrefix.card ≤ XA.card := by
    refine Finset.card_le_card_of_injOn E.chargePrefix ?_ ?_
    · intro p hp
      exact E.chargePrefix_mem p hp
    · intro p hp q hq heq
      exact E.chargePrefix_injective p q hp hq heq
  have hPrefixTail :
      Bprefix.carrier ∩ Tail.tailArc.carrier =
        ({y} : Set (EuclideanSpace ℝ (Fin 2))) := by
    rw [Tail.carrier_eq, hPrefixMeetsTail, hBplusArcTarget]
  obtain ⟨betaArcNew, edgeArcNew, hBetaSource, hBetaTarget,
      hBetaCarrier, hBetaRelative, hPrefixRelativeSubset,
      hTailRelativeSubset, hPrefixCarrierSubset, hTailCarrierSubset,
      hBetaEdge, hOtherEdges, hNewEndpoints, hPrefixToBetaSegments,
      hTailToBetaSegments, hBetaSegmentOwner⟩ :=
    BigonRerouteBetaSpliceAssembly G D beta u y B Bplus Rbeta H Tail Bprefix
      (hPrefixSource.trans hAsource)
      (hPrefixTarget.trans hBplusArcTarget)
      hPrefixTail
  have hxNotTail : x ∉ Tail.tailArc.carrier := by
    intro hxTail
    have hxRbeta : x ∈ Rbeta := by
      rw [← Tail.carrier_eq]
      exact hxTail
    exact Set.disjoint_left.mp hARbeta
      (by simpa [hAcarrier] using hxA) hxRbeta
  obtain ⟨hNewNoVertex, hNewNoThree, hNewCrossingLocalized⟩ :=
    BigonRerouteNewEdgeClassification G D beta u x y B Bplus Rbeta H
      XB E.xPrefix Bprefix betaArcNew edgeArcNew Tail hxCross hxBeta hyBeta hyx
      hBsub hyBplus hBplusCross hBplusNoVertex hXB hxNotTail
      (hPrefixSource.trans hAsource)
      (hPrefixTarget.trans hBplusArcTarget)
      hPrefixNoVertex
      (by
        intro e he p hpPrefix hpEdge
        exact hPrefixContactClassification e he p hpPrefix hpEdge)
      hBetaEdge hOtherEdges hBetaSource hBetaTarget hBetaCarrier hBetaRelative
  obtain ⟨newCrossingSet, hNewCrossingSubset, hNewCrossingSpec,
      hNewTransverse, hNewNoShared⟩ :=
    FiniteLocalizedPolygonalEdgeAssignmentCertification G edgeArcNew
      ((D.crossingSet.erase x \ XB) ∪ E.xPrefix) hNewCrossingLocalized
  have hxNotXB : x ∉ XB := by
    intro hxXB
    exact (hXB x).1 hxXB |>.1.2 (by simp)
  have arc_target_mem_carrier :
      ∀ Q : PolygonalArc, Q.target ∈ Q.carrier := by
    intro Q
    rw [Q.carrier_eq]
    have hlen := Q.length_ge_two
    let m := Q.vertices.length - 2
    have hm : m + 1 < Q.vertices.length := by
      dsimp [m]
      omega
    refine ⟨m, hm, ?_⟩
    have hlast : Q.vertices[m + 1] = Q.target := by
      have ht := Q.target_eq_last
      rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at ht
      have hmLast : m + 1 = Q.vertices.length - 1 := by
        dsimp [m]
        omega
      simpa [hmLast] using Option.some.inj ht
    rw [hlast]
    exact right_mem_segment ℝ Q.vertices[m] Q.target
  have hBetaPair : beta.1 = Sym2.mk u Tail.farEndpoint :=
    (Sym2.mem_and_mem_iff Tail.farEndpoint_ne_u.symm).mp
      ⟨Tail.u_mem_beta, Tail.farEndpoint_mem_beta⟩
  have hOldBetaEndpointSet :
      ({(D.edgeArc beta).source, (D.edgeArc beta).target} :
          Set (EuclideanSpace ℝ (Fin 2))) =
        ({D.vertexPlacement u, D.vertexPlacement Tail.farEndpoint} : Set _) := by
    rcases D.edgeArc_endpoints beta with ⟨a, b, _hab, hEdge, hEnds⟩
    have hSym : Sym2.mk a b = Sym2.mk u Tail.farEndpoint :=
      hEdge.symm.trans hBetaPair
    rcases (Sym2.mk_eq_mk_iff
      (p := (a, b)) (q := (u, Tail.farEndpoint))).mp hSym with hPair | hPair
    · have ha : a = u := congrArg Prod.fst hPair
      have hb : b = Tail.farEndpoint := congrArg Prod.snd hPair
      rcases hEnds with hEnds | hEnds <;>
        ext z <;> simp [hEnds, ha, hb, or_comm]
    · have ha : a = Tail.farEndpoint := congrArg Prod.fst hPair
      have hb : b = u := congrArg Prod.snd hPair
      rcases hEnds with hEnds | hEnds <;>
        ext z <;> simp [hEnds, ha, hb, or_comm]
  have hXBsubset : XB ⊆ D.crossingSet := by
    intro p hpXB
    rcases (hXB p).1 hpXB with ⟨hpRemoved, hpH⟩
    have hpB : p ∈ B := hpRemoved.1
    have hpBetaRelative : p ∈ (D.edgeArc beta).relativeInterior := by
      rw [(D.edgeArc beta).relativeInterior_eq, hOldBetaEndpointSet]
      refine ⟨hBsub hpB, ?_⟩
      intro hpEndpoint
      rcases hpEndpoint with hpu | hpfar
      · exact hpRemoved.2 (by simp [hpu])
      · have hfarTail :
            D.vertexPlacement Tail.farEndpoint ∈ Tail.tailArc.carrier := by
          simpa [Tail.target_eq] using arc_target_mem_carrier Tail.tailArc
        have hfarMeet :
            D.vertexPlacement Tail.farEndpoint ∈
              Tail.tailArc.carrier ∩ (B ∪ Bplus) :=
          ⟨hfarTail, Or.inl (hpfar ▸ hpB)⟩
        rw [Tail.meets_removed_subarc] at hfarMeet
        have hfarY : D.vertexPlacement Tail.farEndpoint = y := by
          simpa using hfarMeet
        have hfarB : D.vertexPlacement Tail.farEndpoint ∈ B := hpfar ▸ hpB
        have hyB : y ∈ B := hfarY ▸ hfarB
        have hyMeet : y ∈ B ∩ Bplus := ⟨hyB, hyBplus⟩
        rw [hBBplus] at hyMeet
        have hyEq : y = x := by simpa using hyMeet
        have hpx : p = x := hpfar.trans (hfarY.trans hyEq)
        exact hpRemoved.2 (by simp [hpx])
    have hpNotVertex : ∀ v : V, p ≠ D.vertexPlacement v := by
      intro v hpv
      exact D.no_vertex_in_edge_interior v beta (hpv ▸ hpBetaRelative)
    rw [hH] at hpH
    rcases hpH with hpEdges | hpVertex
    · rcases Set.mem_iUnion.mp hpEdges with ⟨e, hpe⟩
      by_cases heAlpha : e = alpha
      · subst e
        rw [if_pos rfl] at hpe
        have hpAlphaRelative :=
          oldCarrierOfNonvertexRelative alpha p hpNotVertex hpe.1
        exact (D.crossingSet_spec p).2
          ⟨alpha, beta, hAlphaBeta, hpAlphaRelative, hpBetaRelative⟩
      · by_cases heBeta : e = beta
        · rw [if_neg heAlpha, if_pos heBeta] at hpe
          exact False.elim (hpe.2 (Or.inl hpRemoved))
        · rw [if_neg heAlpha, if_neg heBeta] at hpe
          have hpERelative :=
            oldCarrierOfNonvertexRelative e p hpNotVertex hpe
          exact (D.crossingSet_spec p).2
            ⟨e, beta, heBeta, hpERelative, hpBetaRelative⟩
    · rcases hpVertex with ⟨v, _hvu, hpv⟩
      exact False.elim (hpNotVertex v hpv)
  obtain ⟨D', hDVertex, hDOtherEdges, hDPrefixSubset, hDCount⟩ :=
    BigonRerouteSpliceCount G D beta u x y B Bplus Rbeta H
      XA XB E.xPrefix newCrossingSet Bprefix betaArcNew edgeArcNew Tail
      huBeta hxCross hxNotXB hXBsubset hXnewCard hNewCrossingSubset
      (hPrefixSource.trans hAsource)
      (hPrefixTarget.trans hBplusArcTarget)
      hPrefixTail hBetaEdge hOtherEdges hBetaSource hBetaTarget hBetaCarrier
      hPrefixCarrierSubset hNewEndpoints hNewNoVertex hNewNoThree
      hNewTransverse hNewNoShared hNewCrossingSpec
  refine ⟨Bprefix, D', hDVertex, hDOtherEdges, hDPrefixSubset,
    hPrefixSource.trans hAsource, hPrefixTarget.trans hBplusArcTarget, ?_, ?_,
    ?_, ?_, hDCount⟩
  · simpa [hAcarrier, hAsource] using hPrefixMeetsA
  · simpa [hBarcCarrier, hBplusArcCarrier, hAsource, hBplusArcTarget] using
      hPrefixMeetsRemoved
  · simpa [hBplusArcTarget] using hPrefixMeetsTail
  · intro v hvu hvCarrier
    by_cases hvEnds :
        D.vertexPlacement v ∈
          ({Aarc.source, BplusArc.target} :
            Set (EuclideanSpace ℝ (Fin 2)))
    · rcases hvEnds with hvSource | hvTarget
      · have hvEq : v = u := D.vertexPlacement_injective
          (hvSource.trans hAsource)
        exact hvu hvEq
      · exact hBplusNoVertex v (by
          rw [hvTarget, hBplusArcTarget]
          exact hyBplus)
    · apply hPrefixNoVertex v
      rw [hPrefixRelative]
      exact ⟨hvCarrier, hvEnds⟩
