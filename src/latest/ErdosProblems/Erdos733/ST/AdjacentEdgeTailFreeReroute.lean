import ErdosProblems.Erdos733.ST.BigonReroute
import ErdosProblems.Erdos733.ST.StraightSegmentPolygonalArc
import ErdosProblems.Erdos733.ST.OrdinaryAdjacentEdgesFavorableTailFreeTerminalRefinement
import ErdosProblems.Erdos733.ST.PlaneDrawingSelectedEdgeSourceCappedSectors
import ErdosProblems.Erdos733.ST.OrdinaryAdjacentEdgesSimultaneousBigonGeometryExists
import ErdosProblems.Erdos733.ST.OrdinaryAdjacentEdgesCleanificationConsequences

open Classical
noncomputable section

-- [TABLET NODE: AdjacentEdgeTailFreeReroute]
lemma AdjacentEdgeTailFreeReroute {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet]
    (D : OrdinaryPolygonalDrawing G)
    (alpha beta : G.edgeFinset) (u : V) :
    alpha ≠ beta →
      u ∈ alpha.1 →
        u ∈ beta.1 →
          (∃ x : EuclideanSpace ℝ (Fin 2),
            x ∈ D.crossingSet ∧
              x ∈ (D.edgeArc alpha).relativeInterior ∧
                x ∈ (D.edgeArc beta).relativeInterior) →
            ∃ D' : OrdinaryPolygonalDrawing G,
              D'.crossingSet.card < D.crossingSet.card := by
-- BODY
  intro hab huAlpha huBeta hcross
  rcases hcross with ⟨xOld, hxOld, hxOldAlpha, hxOldBeta⟩
  obtain ⟨Dclean, hvertex, hcard, hclean, hsurvive⟩ :=
    OrdinaryAdjacentEdgesCleanificationConsequences G D alpha beta xOld hxOld
      hab hxOldAlpha hxOldBeta
  by_cases hstrict : Dclean.crossingSet.card < D.crossingSet.card
  · exact ⟨Dclean, hstrict⟩
  have hcardEq : Dclean.crossingSet.card = D.crossingSet.card := by omega
  obtain ⟨xClean, hxClean, hxCleanAlpha, hxCleanBeta⟩ := hsurvive hcardEq
  have hopen : ∀ p : EuclideanSpace ℝ (Fin 2),
      p ∈ Dclean.crossingSet →
        p ∈ (Dclean.edgeArc alpha).relativeInterior →
          p ∈ (Dclean.edgeArc beta).relativeInterior →
            ∃ i j : ℕ,
              ∃ (hi : i + 1 < (Dclean.edgeArc alpha).vertices.length)
                (hj : j + 1 < (Dclean.edgeArc beta).vertices.length),
                p ∈ openSegment ℝ (Dclean.edgeArc alpha).vertices[i]
                    (Dclean.edgeArc alpha).vertices[i + 1] ∧
                  p ∈ openSegment ℝ (Dclean.edgeArc beta).vertices[j]
                    (Dclean.edgeArc beta).vertices[j + 1] := by
    intro p _hp hpAlpha hpBeta
    obtain ⟨i, j, hi, hj, hpOpenAlpha, hpOpenBeta, _hnonparallel⟩ :=
      hclean alpha beta p hab hpAlpha hpBeta
    exact ⟨i, j, hi, hj, hpOpenAlpha, hpOpenBeta⟩
  rcases OrdinaryAdjacentEdgesFavorableTailFreeTerminalRefinement
      G Dclean alpha beta u hopen hab huAlpha huBeta
        ⟨xClean, hxClean, hxCleanAlpha, hxCleanBeta⟩ with
    ⟨firstEdge, secondEdge, hpair, firstArc, secondArc,
      hfirstCarrier, hfirstRelative, hfirstSource,
      hsecondCarrier, hsecondRelative, hsecondSource,
      x, yOld, y, FirstCut, SecondCut, OutCut,
      hx, hxFirst, hxSecond, hyOldSecond, hyOldx,
      hOutCarrier, hAB, hBBplusOld, hFirstTail,
      A, B, BplusOld, RbetaOld, HOld,
      hA, hB, hBplusOld, hRbetaOld, hHOld,
      TailOld, hBplusOldCross, hBplusOldNoVertex,
      XA, XB, hXASpecOld, hXBSpecOld, hXACardXB,
      hxDisk, Disk, hDiskEdges, i, j, hi, hj,
      hxOpenFirst, hxOpenSecond, hnonparallel,
      hyOpen, hBplusBall, Bplus, Rbeta, H,
      hBplus, hRbetaDecomp, hRbeta, hH, Tail,
      hTailCarrier, hATail, hBplusCross, hBplusNoVertex,
      hXASpec, hXBSpec, hXACardXB', hFirstPrefixTransfer⟩
  have hedges : firstEdge ≠ secondEdge := by
    rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hab
    · exact hab.symm
  have huFirst : u ∈ firstEdge.1 := by
    rcases hpair with ⟨rfl, _⟩ | ⟨rfl, _⟩
    · exact huAlpha
    · exact huBeta
  have hyx : y ≠ x := by
    intro hyx
    rw [hyx] at hyOpen
    have hxx := (left_mem_openSegment_iff (𝕜 := ℝ)).1 hyOpen
    exact hyOldx hxx.symm
  have hBplusOldSegment : BplusOld = segment ℝ x yOld :=
    hBplusOld.trans hOutCarrier
  have hBplusSubsetOld : Bplus ⊆ BplusOld := by
    rw [hBplus, hBplusOldSegment]
    exact (convex_segment x yOld).segment_subset
      (left_mem_segment ℝ x yOld)
      (openSegment_subset_segment ℝ x yOld hyOpen)
  have hBplusSub : Bplus ⊆ (Dclean.edgeArc secondEdge).carrier := by
    intro p hp
    rw [hBplusOld, hOutCarrier] at hBplusSubsetOld
    have hpOut : p ∈ OutCut.prefixArc.carrier :=
      hOutCarrier.symm ▸ hBplusSubsetOld hp
    have hpSecondSuffix : p ∈ SecondCut.suffixArc.carrier :=
      OutCut.prefix_carrier_subset hpOut
    have hpSecondArc : p ∈ secondArc.carrier :=
      SecondCut.suffix_carrier_subset hpSecondSuffix
    exact hsecondCarrier ▸ hpSecondArc
  have hBplusRelative : Bplus ⊆
      (Dclean.edgeArc secondEdge).relativeInterior := by
    intro p hp
    rw [(Dclean.edgeArc secondEdge).relativeInterior_eq]
    refine ⟨hBplusSub hp, ?_⟩
    rcases Dclean.edgeArc_endpoints secondEdge with
      ⟨a, b, _habEdge, _hedge, hends⟩
    rcases hends with hends | hends
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨fun h => hBplusNoVertex a (h.trans hends.1 ▸ hp),
        fun h => hBplusNoVertex b (h.trans hends.2 ▸ hp)⟩
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨fun h => hBplusNoVertex b (h.trans hends.1 ▸ hp),
        fun h => hBplusNoVertex a (h.trans hends.2 ▸ hp)⟩
  have hySecond : y ∈ (Dclean.edgeArc secondEdge).relativeInterior :=
    hBplusRelative (hBplus.symm ▸ right_mem_segment ℝ x y)
  have hBplusRel : Bplus \ ({x} : Set _) ⊆
      (Dclean.edgeArc secondEdge).relativeInterior := by
    intro p hp
    exact hBplusRelative hp.1
  have hABExact : A ∩ B = ({Dclean.vertexPlacement u, x} : Set _) := by
    rw [hA, hB]
    exact hAB
  have hBBplusExact : B ∩ Bplus = ({x} : Set _) := by
    apply Set.Subset.antisymm
    · intro p hp
      have hpOld : p ∈ SecondCut.prefixArc.carrier ∩ OutCut.prefixArc.carrier :=
        ⟨hB ▸ hp.1, hBplusOld ▸ hBplusSubsetOld hp.2⟩
      exact hBBplusOld ▸ hpOld
    · intro p hp
      have hpx : p = x := by simpa using hp
      subst p
      refine ⟨?_, ?_⟩
      · rw [hB]
        simpa only [SecondCut.prefix_target] using
          (by
            rw [SecondCut.prefixArc.carrier_eq]
            have hlen := SecondCut.prefixArc.length_ge_two
            let m := SecondCut.prefixArc.vertices.length - 2
            have hm : m + 1 < SecondCut.prefixArc.vertices.length := by
              dsimp [m]
              omega
            refine ⟨m, hm, ?_⟩
            have hlast : SecondCut.prefixArc.vertices[m + 1] = x := by
              have hh := SecondCut.prefixArc.target_eq_last
              rw [List.getLast?_eq_getElem?,
                List.getElem?_eq_getElem (by omega)] at hh
              have hmLast : m + 1 = SecondCut.prefixArc.vertices.length - 1 := by
                dsimp [m]
                omega
              simpa [hmLast, SecondCut.prefix_target] using Option.some.inj hh
            rw [hlast]
            exact right_mem_segment ℝ SecondCut.prefixArc.vertices[m] x)
      · rw [hBplus]
        exact left_mem_segment ℝ x y
  let retainedArc : G.edgeFinset → PolygonalArc := fun e =>
    if e = firstEdge then FirstCut.suffixArc
    else if e = secondEdge then Tail.tailArc
    else Dclean.edgeArc e
  have hBplusBall' : Bplus ⊆ Metric.ball x Disk.radius := by
    rw [hBplus]
    exact hBplusBall
  obtain ⟨Geom⟩ := OrdinaryAdjacentEdgesSimultaneousBigonGeometryExists
    G Dclean u firstEdge secondEdge firstArc secondArc x y FirstCut SecondCut
    A B Bplus Rbeta H Tail retainedArc XA hxDisk Disk hclean hedges
    hfirstCarrier hfirstRelative hfirstSource hsecondCarrier hsecondRelative
    hsecondSource hxFirst hxSecond hySecond hyx hA hB hBplus hABExact
    hBBplusExact hBplusBall' hRbeta hH hATail rfl
    hXASpec hFirstPrefixTransfer hDiskEdges i j hi hj hxOpenFirst hxOpenSecond
    hnonparallel
  have arc_source_mem_carrier (Q : PolygonalArc) : Q.source ∈ Q.carrier := by
    rw [Q.carrier_eq]
    have hlen := Q.length_ge_two
    refine ⟨0, by omega, ?_⟩
    have hzero : Q.vertices[0] = Q.source := by
      have hh := Q.source_eq_head
      rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at hh
      exact Option.some.inj hh
    rw [hzero]
    exact left_mem_segment ℝ Q.source Q.vertices[1]
  have arc_target_mem_carrier (Q : PolygonalArc) : Q.target ∈ Q.carrier := by
    rw [Q.carrier_eq]
    have hlen := Q.length_ge_two
    let m := Q.vertices.length - 2
    have hm : m + 1 < Q.vertices.length := by dsimp [m]; omega
    refine ⟨m, hm, ?_⟩
    have hlast : Q.vertices[m + 1] = Q.target := by
      have hh := Q.target_eq_last
      rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at hh
      have hmLast : m + 1 = Q.vertices.length - 1 := by dsimp [m]; omega
      simpa [hmLast] using Option.some.inj hh
    rw [hlast]
    exact right_mem_segment ℝ Q.vertices[m] Q.target
  have hAsub : A ⊆ (Dclean.edgeArc firstEdge).carrier := by
    rw [hA, ← hfirstCarrier]
    exact FirstCut.prefix_carrier_subset
  have hBsub : B ⊆ (Dclean.edgeArc secondEdge).carrier := by
    rw [hB, ← hsecondCarrier]
    exact SecondCut.prefix_carrier_subset
  have hAcarrier : FirstCut.prefixArc.carrier = A := hA.symm
  have hARbeta : Disjoint FirstCut.prefixArc.carrier Rbeta := by
    simpa only [hA, Tail.carrier_eq] using hATail
  have hAsource : FirstCut.prefixArc.source = Dclean.vertexPlacement u :=
    FirstCut.prefix_source.trans hfirstSource
  have hAtarget : FirstCut.prefixArc.target = x := FirstCut.prefix_target
  have hStartExists :
      ∃ StartSector : Set (EuclideanSpace ℝ (Fin 2)),
        IsOpen StartSector ∧ Convex ℝ StartSector ∧
          StartSector ⊆ Geom.SelectedSide ∧
          Dclean.vertexPlacement u ∈ closure StartSector ∧
          Dclean.vertexPlacement u ∉ StartSector ∧
          StartSector ∩ ((A ∪ B ∪ Bplus ∪ Rbeta ∪ H) ∪ Geom.Bad) = ∅ ∧
          ∀ p, p ∈ XA →
            Disjoint (Metric.closedBall p (Geom.eventRadius p))
              (closure StartSector) := by
    exact ⟨Geom.StartSector, Geom.start_open, Geom.start_convex,
      Geom.start_subset_selected, Geom.source_mem_start_closure,
      Geom.source_not_mem_start, Geom.start_avoids_old,
      Geom.event_balls_avoid_start⟩
  have hBarcExists : ∃ Barc : PolygonalArc,
      Barc.carrier = B ∧ Barc.source = Dclean.vertexPlacement u ∧ Barc.target = x := by
    exact ⟨SecondCut.prefixArc, hB.symm,
      SecondCut.prefix_source.trans hsecondSource, SecondCut.prefix_target⟩
  have hBplusArcExists : ∃ BplusArc : PolygonalArc,
      BplusArc.carrier = Bplus ∧ BplusArc.source = x ∧ BplusArc.target = y := by
    rcases StraightSegmentPolygonalArc x y hyx.symm with
      ⟨BplusArc, hsource, htarget, hcarrier, _hrelative⟩
    exact ⟨BplusArc, hcarrier.trans hBplus.symm, hsource, htarget⟩
  have huA : Dclean.vertexPlacement u ∈ A := by
    rw [hA]
    simpa only [hAsource] using arc_source_mem_carrier FirstCut.prefixArc
  have hxA : x ∈ A := by
    rw [hA]
    simpa only [hAtarget] using arc_target_mem_carrier FirstCut.prefixArc
  have huB : Dclean.vertexPlacement u ∈ B := by
    rw [hB]
    simpa only [SecondCut.prefix_source, hsecondSource] using
      arc_source_mem_carrier SecondCut.prefixArc
  have hxB : x ∈ B := by
    rw [hB]
    simpa only [SecondCut.prefix_target] using
      arc_target_mem_carrier SecondCut.prefixArc
  have hxBplus : x ∈ Bplus := by
    rw [hBplus]
    exact left_mem_segment ℝ x y
  have hyBplus : y ∈ Bplus := by
    rw [hBplus]
    exact right_mem_segment ℝ x y
  have hBadFinite : Set.Finite Geom.Bad := by
    rw [Geom.bad_eq_points]
    exact Geom.Kclean.points.finite_toSet
  have hKExists : ∃ K : FinitePolygonalSet, K.carrier = H :=
    ⟨Geom.Kclean, Geom.kclean_carrier⟩
  have hVerticesH : ∀ v : V, v ≠ u → Dclean.vertexPlacement v ∈ H := by
    intro v hv
    rw [← Geom.kclean_carrier, Geom.Kclean.carrier_eq]
    exact Or.inl (Geom.non_u_vertices_are_points v hv)
  have hCleanExists :
      ∃ Aclean : PolygonalArc, ∃ Kclean : FinitePolygonalSet,
        Aclean = FirstCut.prefixArc ∧ Aclean.carrier = A ∧
        Aclean.source = Dclean.vertexPlacement u ∧ Aclean.target = x ∧
        Kclean.carrier = H ∧
        (∀ v : V, v ≠ u → Dclean.vertexPlacement v ∈ (Kclean.points : Set _)) ∧
        (Kclean.points : Set _) ⊆ Geom.Bad ∧
        (∀ p, p ∈ XA →
          p ∉ (Kclean.points : Set _) ∧
          ∃ j : ℕ, ∃ hj : j + 1 < Aclean.vertices.length,
            p ∈ openSegment ℝ Aclean.vertices[j] Aclean.vertices[j + 1] ∧
            ∃! s : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2),
              s ∈ Kclean.segments ∧ p ∈ openSegment ℝ s.1 s.2 ∧
              ¬ ∃ c : ℝ, s.2 - s.1 =
                c • (Aclean.vertices[j + 1] - Aclean.vertices[j])) ∧
        (∀ p, p ∈ XA →
          0 < Geom.eventRadius p ∧
          Convex ℝ (Geom.SelectedSide ∩ Metric.ball p (Geom.eventRadius p)) ∧
          ∃ s : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2),
            s ∈ Kclean.segments ∧ p ∈ openSegment ℝ s.1 s.2 ∧
            Metric.ball p (Geom.eventRadius p) ∩ H =
              Metric.ball p (Geom.eventRadius p) ∩ segment ℝ s.1 s.2 ∧
            Metric.ball p (Geom.eventRadius p) ∩ Rbeta = ∅) := by
    refine ⟨FirstCut.prefixArc, Geom.Kclean, rfl, hAcarrier, hAsource,
      hAtarget, Geom.kclean_carrier, Geom.non_u_vertices_are_points, ?_,
      Geom.event_clean_segments, Geom.event_local_geometry⟩
    rw [Geom.bad_eq_points]
  have hApproachExists :
      ∃ h : EuclideanSpace ℝ (Fin 2), ∃ Vin : Set (EuclideanSpace ℝ (Fin 2)),
      ∃ predecessor approach : PolygonalArc,
      ∃ lastGate : EuclideanSpace ℝ (Fin 2),
        predecessor.carrier ⊆ Geom.SelectedSide ∩ Vin ∧
        approach.carrier ⊆ Geom.SelectedSide ∩ Vin ∧
        predecessor.target = lastGate ∧ approach.source = lastGate ∧
        predecessor.carrier ∩ approach.carrier = ({lastGate} : Set _) ∧
        approach.target = h ∧
        approach.carrier ∩ segment ℝ h Geom.terminalGate = ({h} : Set _) ∧
        Disjoint predecessor.carrier (segment ℝ h Geom.terminalGate) ∧
        IsOpen Vin ∧ Convex ℝ Vin ∧ h ∈ Vin ∧ h ≠ Geom.terminalGate ∧
        h ∉ A ∪ B ∪ Bplus ∪ Rbeta ∪ H ∪ Geom.Bad ∧
        Vin ⊆ Geom.SelectedSide ∧ x ∈ closure Vin ∧
        (∃ eps : ℝ, 0 < eps ∧
          Geom.SelectedSide ∩ Metric.ball x eps ⊆ Vin) ∧
        Vin ⊆ Geom.DeltaX ∧ Vin ∩ Geom.Qx = ∅ ∧
        Vin ∩ ((A ∪ B ∪ Bplus ∪ Rbeta ∪ H) ∪ Geom.Bad) = ∅ ∧
        Geom.terminalGate ∈ closure Vin ∧ Geom.terminalGate ∉ Vin ∧
        segment ℝ h Geom.terminalGate ⊆ Vin ∪ ({Geom.terminalGate} : Set _) ∧
        openSegment ℝ h Geom.terminalGate ⊆ Vin ∧
        segment ℝ h Geom.terminalGate ∩
          (Geom.TerminalSideRegion ∪ ({Geom.terminalGate} : Set _)) =
            ({Geom.terminalGate} : Set _) ∧
        closure Vin ∩ closure Geom.TerminalSideRegion =
          ({Geom.terminalGate} : Set _) ∧
        closure Vin ∩ closure Geom.TerminalBridgeRegion = ∅ ∧
        Vin ∩ Geom.TerminalSideRegion = ∅ ∧
        ∀ p, p ∈ XA →
          Disjoint (Metric.closedBall p (Geom.eventRadius p)) (closure Vin) := by
    exact ⟨Geom.h, Geom.Vin, Geom.predecessor, Geom.approach, Geom.lastGate,
      Geom.predecessor_subset, Geom.approach_subset, Geom.predecessor_target,
      Geom.approach_source, Geom.predecessor_approach_meet,
      Geom.approach_target, Geom.approach_meets_terminal_segment,
      Geom.predecessor_disjoint_terminal_segment, Geom.vin_open,
      Geom.vin_convex, Geom.h_mem_vin, Geom.h_ne_terminal_gate,
      Geom.h_avoids_old, Geom.vin_subset_selected, Geom.x_mem_vin_closure,
      Geom.selected_near_x_subset_vin, Geom.vin_subset_deltaX,
      Geom.vin_q_disjoint, Geom.vin_avoids_old,
      Geom.terminal_gate_mem_vin_closure, Geom.terminal_gate_not_mem_vin,
      Geom.h_to_terminal_gate_segment, Geom.h_to_terminal_gate_open_segment,
      Geom.h_to_terminal_gate_meets_side, Geom.vin_side_closures,
      Geom.vin_bridge_closures_disjoint, Geom.vin_side_disjoint,
      Geom.event_balls_avoid_vin⟩
  obtain ⟨B', D', _hvertex', _hnonBeta, _hprefix, _hsource, _htarget,
      _hmeetA, _hmeetBB, _hmeetTail, _hnoVertex, hcount⟩ :=
    BigonReroute G Dclean firstEdge secondEdge u x y A B Bplus Rbeta H
      Geom.Bad Geom.DeltaX Geom.Qx Geom.TerminalSideRegion
      Geom.TerminalBridgeRegion Geom.terminalGate Geom.terminalSideSource
      Geom.quadrantGate Geom.eventRadius FirstCut.prefixArc Geom.S
      Geom.SelectedSide XA XB hedges huFirst Tail.u_mem_beta hx hxFirst hxSecond
      hySecond hyx hAsub hBsub hBplusSub hRbeta hH Tail hAcarrier hARbeta
      hAsource hAtarget Geom.selected_side_choice Geom.source_mem_selected_closure
      hStartExists hBarcExists hBplusArcExists huA hxA huB hxB hxBplus hyBplus
      hABExact hBBplusExact hBplusRel hBplusCross
      hBplusNoVertex hBadFinite hKExists hVerticesH hXASpec hCleanExists
      Geom.event_closedBalls_pairwise Geom.selected_avoids_old
      Geom.selected_avoids_terminal_closures Geom.selected_meets_H_only_in_events
      Geom.x_mem_deltaX Geom.y_mem_deltaX Geom.bplus_subset_deltaX
      Geom.q_subset_deltaX Geom.q_convex Geom.q_compact_closure
      Geom.x_mem_q_closure Geom.q_has_nonterminal_point Geom.y_mem_q
      Geom.x_not_mem_q Geom.q_meets_old_only_at_y Geom.terminal_side_open
      Geom.terminal_side_convex Geom.terminal_side_compact_closure
      Geom.terminal_side_subset_deltaX Geom.terminal_side_avoids_old
      Geom.terminal_gate_mem_deltaX Geom.terminal_gate_mem_side_closure
      Geom.terminal_gate_not_mem_side Geom.terminal_gate_not_mem_q
      Geom.terminal_side_source_mem_side_closure
      Geom.terminal_side_source_mem_deltaX Geom.terminal_side_source_not_mem_side
      Geom.terminal_gate_ne_side_source Geom.terminal_side_segment
      Geom.terminal_side_open_segment Geom.terminal_bridge_open
      Geom.terminal_bridge_convex Geom.terminal_bridge_compact_closure
      Geom.terminal_bridge_subset_deltaX Geom.terminal_bridge_avoids_old
      Geom.terminal_side_source_mem_bridge_closure
      Geom.terminal_side_source_not_mem_bridge
      Geom.quadrant_gate_mem_bridge_closure Geom.quadrant_gate_not_mem_bridge
      Geom.terminal_side_source_ne_quadrant_gate Geom.terminal_bridge_segment
      Geom.terminal_bridge_open_segment Geom.quadrant_gate_mem_q
      Geom.quadrant_gate_ne_y Geom.bridge_segment_meets_q_at_gate
      Geom.side_bridge_closures Geom.side_q_closures_disjoint
      Geom.bridge_q_closures Geom.quadrant_to_y_segment
      Geom.quadrant_to_y_avoids_old hApproachExists hXBSpec
  exact ⟨D', by omega⟩
