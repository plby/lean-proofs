import Util.IncidenceGeometry.FinitePolygonalSetCyclicTraversalCuts
import Util.IncidenceGeometry.FinitePolygonalSetCarrierEqSimpleClosedCurvePointsTwo
import Util.IncidenceGeometry.FinitePolygonalSetCyclicListedPointOnElementarySegment
import Util.IncidenceGeometry.FiniteElementarySegmentCutParameterList
import Util.IncidenceGeometry.FinitePolygonalSetCyclicElementarySegmentCutList
import Util.IncidenceGeometry.SimpleClosedPolygonalCurveEdgeArcTraversalList
import Util.IncidenceGeometry.FinitePolygonalSetCyclicElementarySegmentOccurrenceFamily
import Util.IncidenceGeometry.FinitePolygonalSetCyclicGlobalElementaryPieceSkeleton
import Util.IncidenceGeometry.FinitePolygonalSetCyclicGlobalPieceStreamEnumeration
import Util.IncidenceGeometry.FinitePolygonalSetCyclicGlobalPieceStreamTransitionStep
import Util.IncidenceGeometry.FinitePolygonalSetCyclicUnnormalizedListedPointOccurrences
import Util.IncidenceGeometry.FinitePolygonalSetCyclicActualStreamAdjacencyBridge
import Util.IncidenceGeometry.FinitePolygonalSetCyclicActualStreamEndpointContinuityBridge
import Util.IncidenceGeometry.FinitePolygonalSetCyclicSourceOccurrenceCollapse
import Util.IncidenceGeometry.FinitePolygonalSetCyclicSameElementarySegmentSourceSeparation
import Util.IncidenceGeometry.FinitePolygonalSetCyclicPieceSourceNotSegmentTarget
import Util.IncidenceGeometry.FinitePolygonalSetCyclicGlobalSourceSeparation
import Util.IncidenceGeometry.FinitePolygonalSetCyclicActualNormalizedSourceCycle
import Util.IncidenceGeometry.FinitePolygonalSetCyclicNormalizedSourceSuccessorOrder
import Util.IncidenceGeometry.FinitePolygonalSetCyclicFilteredStreamIntervals
import Util.IncidenceGeometry.FinitePolygonalSetCyclicActualStreamIntervalBlocks
import Util.IncidenceGeometry.FinitePolygonalSetCyclicArcCarrierInteriorBasics
import Util.IncidenceGeometry.FinitePolygonalSetCyclicActualArcPieceOrderFacts
import Util.IncidenceGeometry.FinitePolygonalSetCyclicActualPieceCoverage
import Util.IncidenceGeometry.FinitePolygonalSetCyclicActualPieceStreamCases
import Util.IncidenceGeometry.FinitePolygonalSetCyclicStreamPredecessorUnlistedInBlock
import Util.IncidenceGeometry.FinitePolygonalSetCyclicActualPieceStreamBlockUnique
import Util.IncidenceGeometry.FinitePolygonalSetCyclicArcInteriorsDisjointOfPieceIntersectionsListed
import Util.IncidenceGeometry.FinitePolygonalSetCyclicSameArcSeparatedActualPiecesDisjoint
import Util.IncidenceGeometry.FinitePolygonalSetCyclicNonadjacentActualPiecesDisjoint
import Util.IncidenceGeometry.FinitePolygonalSetCyclicResidualEndpointTouch

open Classical
noncomputable section

lemma FinitePolygonalSetCyclicSuccessorOrder
    (J : SimpleClosedPolygonalCurve) (K : FinitePolygonalSet)
    (hKJ : K.carrier = J.carrier) :
    Nonempty (FinitePolygonalSetCyclicTraversalCuts J K) := by
  classical
  rcases FinitePolygonalSetCyclicActualPieceStreamCases J K hKJ with
    ⟨PieceIndex, pieceIndex_fintype, successor, pieceArc, pieceSegmentIndex,
      pieceSource, pieceTarget, pieceSourceParam, pieceTargetParam,
      pieceCarrier, arcPieceOrder, hparam_lt, hsource_eq, htarget_eq,
      hcarrier_eq, hno_listed_open, horder_nonempty, hhead_source,
      hlast_target, hconsecutive, htail_no_source,
      hsource_listed_eq_start, htarget_listed_eq_target, hsuccessor_cycle,
      hsuccessor_nondeg, hpieceCarrier_covers_curve,
      hpiece_mem_arcPieceOrder, pieceStream, hpieceStream_nodup,
      hpieceStream_mem, horder_mem_stream, horder_cases,
      hpieceStream_consecutive, hpieceStream_cyclic,
      hretained_source_unique, hsource_separation_all,
      hsame_elementary_intersections_listed⟩
  letI : Fintype PieceIndex := pieceIndex_fintype
  rcases
    FinitePolygonalSetCyclicArcCarrierInteriorBasics
      J K successor pieceArc pieceSegmentIndex pieceSource pieceTarget
      pieceSourceParam pieceTargetParam hsource_eq htarget_eq pieceCarrier
      hcarrier_eq arcPieceOrder horder_nonempty hhead_source hlast_target
      (by intro p n hn; exact (hconsecutive p n hn).1)
      htail_no_source hsource_listed_eq_start htarget_listed_eq_target
      hpieceCarrier_covers_curve hpiece_mem_arcPieceOrder hno_listed_open with
    ⟨arcCarrier, arcInterior, harcCarrier_eq, hopen_subset, hjunction_mem,
      hstart_mem, htarget_mem, harc_in_curve, hcurve_covered,
      harcInterior_eq, hno_listed_in_interior⟩
  have hblock_unique :
      ∀ p q : {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points},
        ∀ i : PieceIndex, i ∈ arcPieceOrder p → i ∈ arcPieceOrder q →
          p = q :=
    FinitePolygonalSetCyclicActualPieceStreamBlockUnique
      K successor pieceSource arcPieceOrder pieceStream hpieceStream_nodup
      hsource_listed_eq_start horder_cases
  have hcyclic_predecessor_unlisted_same_block :
      ∀ p q : {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points},
        ∀ i j : PieceIndex, i ∈ arcPieceOrder p → j ∈ arcPieceOrder q →
          ((∃ (n : ℕ) (hn : n + 1 < pieceStream.length),
              pieceStream[n] = i ∧ pieceStream[n + 1] = j) ∨
            (pieceStream.getLast? = some i ∧ pieceStream.head? = some j)) →
            pieceSource j ∉ K.points → p = q := by
    intro p q i j hi hj hadj hsrcj
    exact
      hblock_unique p q i hi
        (FinitePolygonalSetCyclicStreamPredecessorUnlistedInBlock
          (points := K.points) (successor := successor)
          (pieceSource := pieceSource) (arcPieceOrder := arcPieceOrder)
          (pieceStream := pieceStream) hpieceStream_nodup horder_cases
          q i j hj hadj hsrcj)
  have harcInteriors_disjoint :
      ∀ p q : {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points},
        p ≠ q → Disjoint (arcInterior p) (arcInterior q) := by
    have hsame_arc_separated_disjoint :
        ∀ i j : PieceIndex, pieceArc i = pieceArc j →
          (pieceSegmentIndex i).1 + 1 < (pieceSegmentIndex j).1 →
            Disjoint (pieceCarrier i) (pieceCarrier j) := by
      intro i j hsame hgap
      exact
        FinitePolygonalSetCyclicSameArcSeparatedActualPiecesDisjoint
          J pieceArc pieceSegmentIndex pieceSource pieceTarget
          pieceSourceParam pieceTargetParam hsource_eq htarget_eq
          pieceCarrier hcarrier_eq i j hsame hgap
    have hnonadjacent_piece_disjoint :
        ∀ i j : PieceIndex, pieceArc j ≠ pieceArc i →
          pieceArc j ≠ J.successor (pieceArc i) →
            J.successor (pieceArc j) ≠ pieceArc i →
              Disjoint (pieceCarrier i) (pieceCarrier j) := by
      intro i j hneq hnot_succ hnot_pred
      exact
        FinitePolygonalSetCyclicNonadjacentActualPiecesDisjoint
          J pieceArc pieceSegmentIndex pieceSource pieceTarget
          pieceSourceParam pieceTargetParam hsource_eq htarget_eq
          pieceCarrier hcarrier_eq i j hneq hnot_succ hnot_pred
    have hresidual_touching_piece_intersections_listed :
        ∀ p q : {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points},
          p ≠ q →
            ∀ i j : PieceIndex, i ≠ j →
              i ∈ arcPieceOrder p → j ∈ arcPieceOrder q →
                ¬ (pieceArc i = pieceArc j ∧
                  ((pieceSegmentIndex i).1 + 1 < (pieceSegmentIndex j).1 ∨
                    (pieceSegmentIndex j).1 + 1 < (pieceSegmentIndex i).1)) →
                ¬ (pieceArc j ≠ pieceArc i ∧
                  pieceArc j ≠ J.successor (pieceArc i) ∧
                  J.successor (pieceArc j) ≠ pieceArc i) →
                ∀ x : EuclideanSpace ℝ (Fin 2),
                  x ∈ pieceCarrier i → x ∈ pieceCarrier j → x ∈ K.points := by
      intro p q hpq i j hij hi hj hnot_same_separated hnot_nonadjacent x hxi hxj
      by_cases hsame_elementary :
          pieceArc i = pieceArc j ∧
            (pieceSegmentIndex i).1 = (pieceSegmentIndex j).1
      · exact
          hsame_elementary_intersections_listed i j hij hsame_elementary.1
            hsame_elementary.2 x hxi hxj
      ·
        -- Remaining residual geometric cases: adjacent elementary segments on
        -- one edge arc, and the two oriented adjacent-edge-arc endpoint cases.
        have hlisted_of_known_forward_touch :
            (((∃ (n : ℕ) (hn : n + 1 < pieceStream.length),
                pieceStream[n] = i ∧ pieceStream[n + 1] = j) ∨
              (pieceStream.getLast? = some i ∧ pieceStream.head? = some j)) →
              x = pieceSource j → x ∈ K.points) := by
          intro hadj hxsource
          by_cases hsrcj : pieceSource j ∈ K.points
          · simpa [hxsource] using hsrcj
          · have hpq' :=
              hcyclic_predecessor_unlisted_same_block p q i j hi hj hadj hsrcj
            exact False.elim (hpq hpq')
        have hlisted_of_known_reverse_touch :
            (((∃ (n : ℕ) (hn : n + 1 < pieceStream.length),
                pieceStream[n] = j ∧ pieceStream[n + 1] = i) ∨
              (pieceStream.getLast? = some j ∧ pieceStream.head? = some i)) →
              x = pieceSource i → x ∈ K.points) := by
          intro hadj hxsource
          by_cases hsrci : pieceSource i ∈ K.points
          · simpa [hxsource] using hsrci
          · have hqp :=
              hcyclic_predecessor_unlisted_same_block q p j i hj hi hadj hsrci
            exact False.elim (hpq hqp.symm)
        have hlisted_of_forward_endpoint :
            x = pieceTarget i → x = pieceSource j → x ∈ K.points := by
          intro hxtarget hxsource
          rcases List.getElem_of_mem (hpieceStream_mem i) with ⟨n, hn, hgeti⟩
          by_cases hnnext : n + 1 < pieceStream.length
          · have hjoin := (hpieceStream_consecutive n hnnext).1
            have hsame_source :
                pieceSource pieceStream[n + 1] = pieceSource j := by
              calc
                pieceSource pieceStream[n + 1] = pieceTarget pieceStream[n] := hjoin.symm
                _ = pieceTarget i := by rw [hgeti]
                _ = x := hxtarget.symm
                _ = pieceSource j := hxsource
            have hnext_eq : pieceStream[n + 1] = j :=
              hsource_separation_all pieceStream[n + 1] j hsame_source
            exact
              hlisted_of_known_forward_touch
                (Or.inl ⟨n, hnnext, hgeti, hnext_eq⟩) hxsource
          · have hnlast : n + 1 = pieceStream.length := by omega
            have hlast : pieceStream.getLast? = some i := by
              rw [List.getLast?_eq_getElem?]
              have hidx : pieceStream.length - 1 = n := by omega
              rw [hidx, List.getElem?_eq_getElem hn]
              exact congrArg some hgeti
            have hpos : 0 < pieceStream.length := by omega
            let first : PieceIndex := pieceStream[0]
            have hhead : pieceStream.head? = some first := by
              rw [List.head?_eq_getElem?]
              simp [first, hpos]
            have hjoin := (hpieceStream_cyclic i hlast first hhead).1
            have hsame_source : pieceSource first = pieceSource j := by
              calc
                pieceSource first = pieceTarget i := hjoin.symm
                _ = x := hxtarget.symm
                _ = pieceSource j := hxsource
            have hfirst_eq : first = j :=
              hsource_separation_all first j hsame_source
            exact
              hlisted_of_known_forward_touch
                (Or.inr ⟨hlast, by simpa [hfirst_eq] using hhead⟩) hxsource
        have hlisted_of_reverse_endpoint :
            x = pieceTarget j → x = pieceSource i → x ∈ K.points := by
          intro hxtarget hxsource
          rcases List.getElem_of_mem (hpieceStream_mem j) with ⟨n, hn, hgetj⟩
          by_cases hnnext : n + 1 < pieceStream.length
          · have hjoin := (hpieceStream_consecutive n hnnext).1
            have hsame_source :
                pieceSource pieceStream[n + 1] = pieceSource i := by
              calc
                pieceSource pieceStream[n + 1] = pieceTarget pieceStream[n] := hjoin.symm
                _ = pieceTarget j := by rw [hgetj]
                _ = x := hxtarget.symm
                _ = pieceSource i := hxsource
            have hnext_eq : pieceStream[n + 1] = i :=
              hsource_separation_all pieceStream[n + 1] i hsame_source
            exact
              hlisted_of_known_reverse_touch
                (Or.inl ⟨n, hnnext, hgetj, hnext_eq⟩) hxsource
          · have hnlast : n + 1 = pieceStream.length := by omega
            have hlast : pieceStream.getLast? = some j := by
              rw [List.getLast?_eq_getElem?]
              have hidx : pieceStream.length - 1 = n := by omega
              rw [hidx, List.getElem?_eq_getElem hn]
              exact congrArg some hgetj
            have hpos : 0 < pieceStream.length := by omega
            let first : PieceIndex := pieceStream[0]
            have hhead : pieceStream.head? = some first := by
              rw [List.head?_eq_getElem?]
              simp [first, hpos]
            have hjoin := (hpieceStream_cyclic j hlast first hhead).1
            have hsame_source : pieceSource first = pieceSource i := by
              calc
                pieceSource first = pieceTarget j := hjoin.symm
                _ = x := hxtarget.symm
                _ = pieceSource i := hxsource
            have hfirst_eq : first = i :=
              hsource_separation_all first i hsame_source
            exact
              hlisted_of_known_reverse_touch
                (Or.inr ⟨hlast, by simpa [hfirst_eq] using hhead⟩) hxsource
        have hendpoint_touch :=
          FinitePolygonalSetCyclicResidualEndpointTouch
            J pieceArc pieceSegmentIndex pieceSource pieceTarget
            pieceSourceParam pieceTargetParam hparam_lt hsource_eq htarget_eq
            pieceCarrier hcarrier_eq i j hsame_elementary
            hnot_same_separated hnot_nonadjacent x hxi hxj
        rcases hendpoint_touch with hforward | hreverse
        · exact hlisted_of_forward_endpoint hforward.1 hforward.2
        · exact hlisted_of_reverse_endpoint hreverse.1 hreverse.2
    have hdistinct_piece_intersections_listed :
        ∀ p q : {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points},
          p ≠ q →
            ∀ i j : PieceIndex, i ≠ j →
              i ∈ arcPieceOrder p → j ∈ arcPieceOrder q →
                ∀ x : EuclideanSpace ℝ (Fin 2),
                  x ∈ pieceCarrier i → x ∈ pieceCarrier j → x ∈ K.points := by
      intro p q hpq i j hij hi hj x hxi hxj
      by_cases hsame_separated :
          pieceArc i = pieceArc j ∧
            ((pieceSegmentIndex i).1 + 1 < (pieceSegmentIndex j).1 ∨
              (pieceSegmentIndex j).1 + 1 < (pieceSegmentIndex i).1)
      · rcases hsame_separated with ⟨hsame, hgap | hgap⟩
        · have hdisj := hsame_arc_separated_disjoint i j hsame hgap
          exact False.elim ((Set.disjoint_left.mp hdisj) hxi hxj)
        · have hdisj := hsame_arc_separated_disjoint j i hsame.symm hgap
          exact False.elim ((Set.disjoint_left.mp hdisj) hxj hxi)
      · by_cases hnonadjacent :
            pieceArc j ≠ pieceArc i ∧
              pieceArc j ≠ J.successor (pieceArc i) ∧
              J.successor (pieceArc j) ≠ pieceArc i
        · rcases hnonadjacent with ⟨hneq, hnot_succ, hnot_pred⟩
          have hdisj := hnonadjacent_piece_disjoint i j hneq hnot_succ hnot_pred
          exact False.elim ((Set.disjoint_left.mp hdisj) hxi hxj)
        · exact
            hresidual_touching_piece_intersections_listed p q hpq i j hij
              hi hj hsame_separated hnonadjacent x hxi hxj
    have hpiece_intersections_listed :
        ∀ p q : {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points},
          p ≠ q →
            ∀ i j : PieceIndex, i ∈ arcPieceOrder p → j ∈ arcPieceOrder q →
              ∀ x : EuclideanSpace ℝ (Fin 2),
                x ∈ pieceCarrier i → x ∈ pieceCarrier j → x ∈ K.points := by
      intro p q hpq i j hi hj x hxi hxj
      by_cases hij : i = j
      · subst j
        exact False.elim (hpq (hblock_unique p q i hi hj))
      · exact hdistinct_piece_intersections_listed p q hpq i j hij hi hj x hxi hxj
    exact
      FinitePolygonalSetCyclicArcInteriorsDisjointOfPieceIntersectionsListed
        K successor pieceCarrier arcPieceOrder arcCarrier arcInterior
        harcCarrier_eq harcInterior_eq hno_listed_in_interior
        hpiece_intersections_listed
  exact ⟨{
    successor := successor
    arcCarrier := arcCarrier
    arcInterior := arcInterior
    pieceIndex := PieceIndex
    pieceIndex_fintype := pieceIndex_fintype
    pieceArc := pieceArc
    pieceSegmentIndex := pieceSegmentIndex
    pieceSource := pieceSource
    pieceTarget := pieceTarget
    pieceSourceParam := pieceSourceParam
    pieceTargetParam := pieceTargetParam
    pieceSourceParam_lt_targetParam := hparam_lt
    pieceSource_eq := hsource_eq
    pieceTarget_eq := htarget_eq
    pieceCarrier := pieceCarrier
    pieceCarrier_eq := hcarrier_eq
    arcPieceOrder := arcPieceOrder
    arcPieceOrder_nonempty := horder_nonempty
    arcPieceOrder_head_source := hhead_source
    arcPieceOrder_last_target := hlast_target
    arcPieceOrder_consecutive := hconsecutive
    arcCarrier_eq_pieceOrder := harcCarrier_eq
    ordered_piece_open_subset_arcInterior := hopen_subset
    ordered_consecutive_junction_mem_arcInterior := hjunction_mem
    successor_single_cycle := hsuccessor_cycle
    successor_nondegenerate := hsuccessor_nondeg
    arc_start_mem := hstart_mem
    arc_target_mem := htarget_mem
    arc_in_curve := harc_in_curve
    curve_covered_by_arcs := hcurve_covered
    arcInterior_eq := harcInterior_eq
    no_listed_point_in_arcInterior := hno_listed_in_interior
    arcInteriors_disjoint := harcInteriors_disjoint
  }⟩
