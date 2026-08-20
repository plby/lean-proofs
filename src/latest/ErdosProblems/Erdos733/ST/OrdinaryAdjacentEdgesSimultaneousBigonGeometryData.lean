import ErdosProblems.Erdos733.ST.FinitePolygonalSet
import ErdosProblems.Erdos733.ST.OrdinaryLabeledCrossingDiskData
import ErdosProblems.Erdos733.ST.PolygonalSideStrips

open Classical
noncomputable section

-- [TABLET NODE: OrdinaryAdjacentEdgesSimultaneousBigonGeometryData]
structure OrdinaryAdjacentEdgesSimultaneousBigonGeometryData
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet]
    (D : OrdinaryPolygonalDrawing G)
    (u : V) (firstEdge secondEdge : G.edgeFinset)
    (x y : EuclideanSpace ℝ (Fin 2))
    (A B Bplus Rbeta H : Set (EuclideanSpace ℝ (Fin 2)))
    (Aarc : PolygonalArc)
    (XA : Finset (EuclideanSpace ℝ (Fin 2)))
    (hx : x ∈ D.crossingSet)
    (Disk : OrdinaryLabeledCrossingDiskData G D ⟨x, hx⟩) where
-- BODY
  Kclean : FinitePolygonalSet
  Bad : Set (EuclideanSpace ℝ (Fin 2))
  DeltaX : Set (EuclideanSpace ℝ (Fin 2))
  eventRadius : EuclideanSpace ℝ (Fin 2) → ℝ
  S : PolygonalSideStrips Aarc
  SelectedSide : Set (EuclideanSpace ℝ (Fin 2))
  StartSector : Set (EuclideanSpace ℝ (Fin 2))
  Qx : Set (EuclideanSpace ℝ (Fin 2))
  TerminalSideRegion : Set (EuclideanSpace ℝ (Fin 2))
  TerminalBridgeRegion : Set (EuclideanSpace ℝ (Fin 2))
  terminalGate : EuclideanSpace ℝ (Fin 2)
  terminalSideSource : EuclideanSpace ℝ (Fin 2)
  quadrantGate : EuclideanSpace ℝ (Fin 2)
  h : EuclideanSpace ℝ (Fin 2)
  Vin : Set (EuclideanSpace ℝ (Fin 2))
  predecessor : PolygonalArc
  approach : PolygonalArc
  lastGate : EuclideanSpace ℝ (Fin 2)
  kclean_carrier : Kclean.carrier = H
  bad_eq_points : Bad = (Kclean.points : Set _)
  deltaX_eq : DeltaX = Metric.ball x Disk.radius
  non_u_vertices_are_points :
    ∀ v : V, v ≠ u → D.vertexPlacement v ∈ (Kclean.points : Set _)
  event_clean_segments :
    ∀ p : EuclideanSpace ℝ (Fin 2), p ∈ XA →
      p ∉ (Kclean.points : Set _) ∧
        ∃ j : ℕ, ∃ hj : j + 1 < Aarc.vertices.length,
          p ∈ openSegment ℝ Aarc.vertices[j] Aarc.vertices[j + 1] ∧
            ∃! s : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2),
              s ∈ Kclean.segments ∧
                p ∈ openSegment ℝ s.1 s.2 ∧
                  ¬ ∃ c : ℝ, s.2 - s.1 =
                    c • (Aarc.vertices[j + 1] - Aarc.vertices[j])
  selected_side_choice :
    SelectedSide = S.leftStrip ∨ SelectedSide = S.rightStrip
  source_mem_selected_closure : D.vertexPlacement u ∈ closure SelectedSide
  start_open : IsOpen StartSector
  start_convex : Convex ℝ StartSector
  start_subset_selected : StartSector ⊆ SelectedSide
  source_mem_start_closure : D.vertexPlacement u ∈ closure StartSector
  source_not_mem_start : D.vertexPlacement u ∉ StartSector
  start_avoids_old :
    StartSector ∩ ((A ∪ B ∪ Bplus ∪ Rbeta ∪ H) ∪ Bad) = ∅
  event_balls_avoid_start :
    ∀ p : EuclideanSpace ℝ (Fin 2), p ∈ XA →
      Disjoint (Metric.closedBall p (eventRadius p)) (closure StartSector)
  event_local_geometry :
    ∀ p : EuclideanSpace ℝ (Fin 2), p ∈ XA →
      0 < eventRadius p ∧
        Convex ℝ (SelectedSide ∩ Metric.ball p (eventRadius p)) ∧
          ∃ s : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2),
            s ∈ Kclean.segments ∧
              p ∈ openSegment ℝ s.1 s.2 ∧
                Metric.ball p (eventRadius p) ∩ H =
                  Metric.ball p (eventRadius p) ∩ segment ℝ s.1 s.2 ∧
                Metric.ball p (eventRadius p) ∩ Rbeta = ∅
  event_closedBalls_pairwise :
    ∀ p q : EuclideanSpace ℝ (Fin 2),
      p ∈ XA → q ∈ XA → p ≠ q →
        Disjoint (Metric.closedBall p (eventRadius p))
          (Metric.closedBall q (eventRadius q))
  selected_avoids_old : SelectedSide ∩ (B ∪ Bplus ∪ Rbeta ∪ Bad) = ∅
  selected_avoids_terminal_closures :
    SelectedSide ∩
      (closure TerminalSideRegion ∪ closure TerminalBridgeRegion ∪ closure Qx) = ∅
  selected_meets_H_only_in_events :
    SelectedSide ∩ H ⊆
      ⋃ p ∈ (XA : Set (EuclideanSpace ℝ (Fin 2))),
        Metric.ball p (eventRadius p)
  x_mem_deltaX : x ∈ DeltaX
  y_mem_deltaX : y ∈ DeltaX
  bplus_subset_deltaX : Bplus ⊆ DeltaX
  q_subset_deltaX : Qx ⊆ DeltaX
  q_convex : Convex ℝ Qx
  q_compact_closure : IsCompact (closure Qx)
  x_mem_q_closure : x ∈ closure Qx
  q_has_nonterminal_point : ∃ q : EuclideanSpace ℝ (Fin 2), q ∈ Qx ∧ q ≠ y
  y_mem_q : y ∈ Qx
  x_not_mem_q : x ∉ Qx
  q_meets_old_only_at_y : Qx ∩ (A ∪ B ∪ Bplus ∪ Rbeta ∪ H) = ({y} : Set _)
  terminal_side_open : IsOpen TerminalSideRegion
  terminal_side_convex : Convex ℝ TerminalSideRegion
  terminal_side_compact_closure : IsCompact (closure TerminalSideRegion)
  terminal_side_subset_deltaX : TerminalSideRegion ⊆ DeltaX
  terminal_side_avoids_old :
    (TerminalSideRegion ∪ ({terminalGate, terminalSideSource} : Set _)) ∩
      ((A ∪ B ∪ Bplus ∪ Rbeta ∪ H) ∪ Bad) = ∅
  terminal_gate_mem_deltaX : terminalGate ∈ DeltaX
  terminal_gate_mem_side_closure : terminalGate ∈ closure TerminalSideRegion
  terminal_gate_not_mem_side : terminalGate ∉ TerminalSideRegion
  terminal_gate_not_mem_q : terminalGate ∉ Qx
  terminal_side_source_mem_side_closure :
    terminalSideSource ∈ closure TerminalSideRegion
  terminal_side_source_mem_deltaX : terminalSideSource ∈ DeltaX
  terminal_side_source_not_mem_side : terminalSideSource ∉ TerminalSideRegion
  terminal_gate_ne_side_source : terminalGate ≠ terminalSideSource
  terminal_side_segment :
    segment ℝ terminalGate terminalSideSource ⊆
      TerminalSideRegion ∪ ({terminalGate, terminalSideSource} : Set _)
  terminal_side_open_segment :
    openSegment ℝ terminalGate terminalSideSource ⊆ TerminalSideRegion
  terminal_bridge_open : IsOpen TerminalBridgeRegion
  terminal_bridge_convex : Convex ℝ TerminalBridgeRegion
  terminal_bridge_compact_closure : IsCompact (closure TerminalBridgeRegion)
  terminal_bridge_subset_deltaX : TerminalBridgeRegion ⊆ DeltaX
  terminal_bridge_avoids_old :
    (TerminalBridgeRegion ∪ ({terminalSideSource, quadrantGate} : Set _)) ∩
      ((A ∪ B ∪ Bplus ∪ Rbeta ∪ H) ∪ Bad) = ∅
  terminal_side_source_mem_bridge_closure :
    terminalSideSource ∈ closure TerminalBridgeRegion
  terminal_side_source_not_mem_bridge : terminalSideSource ∉ TerminalBridgeRegion
  quadrant_gate_mem_bridge_closure : quadrantGate ∈ closure TerminalBridgeRegion
  quadrant_gate_not_mem_bridge : quadrantGate ∉ TerminalBridgeRegion
  terminal_side_source_ne_quadrant_gate : terminalSideSource ≠ quadrantGate
  terminal_bridge_segment :
    segment ℝ terminalSideSource quadrantGate ⊆
      TerminalBridgeRegion ∪ ({terminalSideSource, quadrantGate} : Set _)
  terminal_bridge_open_segment :
    openSegment ℝ terminalSideSource quadrantGate ⊆ TerminalBridgeRegion
  quadrant_gate_mem_q : quadrantGate ∈ Qx
  quadrant_gate_ne_y : quadrantGate ≠ y
  bridge_segment_meets_q_at_gate :
    segment ℝ terminalSideSource quadrantGate ∩ Qx = ({quadrantGate} : Set _)
  side_bridge_closures :
    closure TerminalSideRegion ∩ closure TerminalBridgeRegion =
      ({terminalSideSource} : Set _)
  side_q_closures_disjoint : closure TerminalSideRegion ∩ closure Qx = ∅
  bridge_q_closures :
    closure TerminalBridgeRegion ∩ closure Qx = ({quadrantGate} : Set _)
  quadrant_to_y_segment : segment ℝ quadrantGate y ⊆ Qx
  quadrant_to_y_avoids_old :
    openSegment ℝ quadrantGate y ∩
      ((A ∪ B ∪ Bplus ∪ Rbeta ∪ H) ∪ Bad) = ∅
  predecessor_subset : predecessor.carrier ⊆ SelectedSide ∩ Vin
  approach_subset : approach.carrier ⊆ SelectedSide ∩ Vin
  predecessor_target : predecessor.target = lastGate
  approach_source : approach.source = lastGate
  predecessor_approach_meet :
    predecessor.carrier ∩ approach.carrier = ({lastGate} : Set _)
  approach_target : approach.target = h
  approach_meets_terminal_segment :
    approach.carrier ∩ segment ℝ h terminalGate = ({h} : Set _)
  predecessor_disjoint_terminal_segment :
    Disjoint predecessor.carrier (segment ℝ h terminalGate)
  vin_open : IsOpen Vin
  vin_convex : Convex ℝ Vin
  h_mem_vin : h ∈ Vin
  h_ne_terminal_gate : h ≠ terminalGate
  h_avoids_old : h ∉ A ∪ B ∪ Bplus ∪ Rbeta ∪ H ∪ Bad
  vin_subset_selected : Vin ⊆ SelectedSide
  x_mem_vin_closure : x ∈ closure Vin
  selected_near_x_subset_vin :
    ∃ eps : ℝ, 0 < eps ∧ SelectedSide ∩ Metric.ball x eps ⊆ Vin
  vin_subset_deltaX : Vin ⊆ DeltaX
  vin_q_disjoint : Vin ∩ Qx = ∅
  vin_avoids_old : Vin ∩ ((A ∪ B ∪ Bplus ∪ Rbeta ∪ H) ∪ Bad) = ∅
  terminal_gate_mem_vin_closure : terminalGate ∈ closure Vin
  terminal_gate_not_mem_vin : terminalGate ∉ Vin
  h_to_terminal_gate_segment :
    segment ℝ h terminalGate ⊆ Vin ∪ ({terminalGate} : Set _)
  h_to_terminal_gate_open_segment : openSegment ℝ h terminalGate ⊆ Vin
  h_to_terminal_gate_meets_side :
    segment ℝ h terminalGate ∩
      (TerminalSideRegion ∪ ({terminalGate} : Set _)) = ({terminalGate} : Set _)
  vin_side_closures :
    closure Vin ∩ closure TerminalSideRegion = ({terminalGate} : Set _)
  vin_bridge_closures_disjoint : closure Vin ∩ closure TerminalBridgeRegion = ∅
  vin_side_disjoint : Vin ∩ TerminalSideRegion = ∅
  event_balls_avoid_vin :
    ∀ p : EuclideanSpace ℝ (Fin 2), p ∈ XA →
      Disjoint (Metric.closedBall p (eventRadius p)) (closure Vin)
