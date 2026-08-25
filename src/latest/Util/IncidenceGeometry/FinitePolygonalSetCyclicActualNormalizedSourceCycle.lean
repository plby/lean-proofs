import Util.IncidenceGeometry.FinitePolygonalSetCyclicGlobalPieceStreamEnumeration
import Util.IncidenceGeometry.FinitePolygonalSetCyclicUnnormalizedListedPointOccurrences
import Util.IncidenceGeometry.FinitePolygonalSetCyclicActualStreamEndpointContinuityBridge
import Util.IncidenceGeometry.FinitePolygonalSetCyclicSourceOccurrenceCollapse
import Util.IncidenceGeometry.FinitePolygonalSetCyclicGlobalSourceSeparation
import Mathlib.Data.List.Nodup

open Classical
noncomputable section


lemma FinitePolygonalSetCyclicActualNormalizedSourceCycle
    (J : SimpleClosedPolygonalCurve) (K : FinitePolygonalSet)
    (hKJ : K.carrier = J.carrier)
    (E : List {γ : PolygonalArc // γ ∈ J.edgeArcs})
    (hEnodup : E.Nodup)
    (hEall : ∀ γ : {γ : PolygonalArc // γ ∈ J.edgeArcs}, γ ∈ E)
    (hEpos : 0 < E.length)
    (hEsucc : ∀ n (hn : n + 1 < E.length),
      J.successor (E[n]) = E[n + 1])
    (hEwrap : ∀ (hLast : E.length - 1 < E.length) (hFirst : 0 < E.length),
      J.successor (E[E.length - 1]'hLast) = E[0]'hFirst)
    (segmentIndex_lt :
      (e : Fin E.length) →
        (n : Fin ((E[e.1]'e.2).1.vertices.length - 1)) →
          n.1 + 1 < (E[e.1]'e.2).1.vertices.length)
    (cutList :
      (e : Fin E.length) →
        Fin ((E[e.1]'e.2).1.vertices.length - 1) → List ℝ)
    (cutList_nodup : ∀ e n, (cutList e n).Nodup)
    (cutList_sorted : ∀ e n, (cutList e n).SortedLT)
    (cutList_mem :
      ∀ e n (t : ℝ), t ∈ cutList e n ↔
        t = 0 ∨ t = 1 ∨
          (0 ≤ t ∧ t ≤ 1 ∧
            AffineMap.lineMap
              ((E[e.1]'e.2).1.vertices[n.1]'
                (Nat.lt_of_succ_lt (segmentIndex_lt e n)))
              ((E[e.1]'e.2).1.vertices[n.1 + 1]'
                (segmentIndex_lt e n)) t ∈ K.points))
    (cutList_zero : ∀ e n, (0 : ℝ) ∈ cutList e n)
    (cutList_one : ∀ e n, (1 : ℝ) ∈ cutList e n)
    (cutList_bounds : ∀ e n t, t ∈ cutList e n → 0 ≤ t ∧ t ≤ 1)
    (localPieceIndex :
      (e : Fin E.length) →
        Fin ((E[e.1]'e.2).1.vertices.length - 1) → Type)
    (pieceNumber :
      (Sigma (fun e : Fin E.length =>
        Sigma (fun n : Fin ((E[e.1]'e.2).1.vertices.length - 1) =>
          localPieceIndex e n))) → ℕ)
    (pieceNumber_lt :
      ∀ i : Sigma (fun e : Fin E.length =>
        Sigma (fun n : Fin ((E[e.1]'e.2).1.vertices.length - 1) =>
          localPieceIndex e n)),
        pieceNumber i + 1 < (cutList i.1 i.2.1).length)
    (pieceNumber_surjective :
      ∀ e n k (_hk : k + 1 < (cutList e n).length),
        ∃ a : localPieceIndex e n, pieceNumber ⟨e, ⟨n, a⟩⟩ = k)
    (pieceNumber_injective :
      ∀ e n (a b : localPieceIndex e n),
        pieceNumber ⟨e, ⟨n, a⟩⟩ =
          pieceNumber ⟨e, ⟨n, b⟩⟩ →
        a = b)
    (pieceSourceParam :
      (Sigma (fun e : Fin E.length =>
        Sigma (fun n : Fin ((E[e.1]'e.2).1.vertices.length - 1) =>
          localPieceIndex e n))) → Set.Icc (0 : ℝ) 1)
    (pieceTargetParam :
      (Sigma (fun e : Fin E.length =>
        Sigma (fun n : Fin ((E[e.1]'e.2).1.vertices.length - 1) =>
          localPieceIndex e n))) → Set.Icc (0 : ℝ) 1)
    (pieceSourceParam_lt :
      ∀ i : Sigma (fun e : Fin E.length =>
        Sigma (fun n : Fin ((E[e.1]'e.2).1.vertices.length - 1) =>
          localPieceIndex e n)),
        pieceSourceParam i < pieceTargetParam i)
    (pieceSourceParam_eq :
      ∀ i : Sigma (fun e : Fin E.length =>
        Sigma (fun n : Fin ((E[e.1]'e.2).1.vertices.length - 1) =>
          localPieceIndex e n)),
        (pieceSourceParam i).1 =
          (cutList i.1 i.2.1)[pieceNumber i]'
            (Nat.lt_of_succ_lt (pieceNumber_lt i)))
    (pieceTargetParam_eq :
      ∀ i : Sigma (fun e : Fin E.length =>
        Sigma (fun n : Fin ((E[e.1]'e.2).1.vertices.length - 1) =>
          localPieceIndex e n)),
        (pieceTargetParam i).1 =
          (cutList i.1 i.2.1)[pieceNumber i + 1]'
            (pieceNumber_lt i))
    (pieceArc :
      (Sigma (fun e : Fin E.length =>
        Sigma (fun n : Fin ((E[e.1]'e.2).1.vertices.length - 1) =>
          localPieceIndex e n))) →
        {γ : PolygonalArc // γ ∈ J.edgeArcs})
    (pieceSegmentIndex :
      (i : Sigma (fun e : Fin E.length =>
        Sigma (fun n : Fin ((E[e.1]'e.2).1.vertices.length - 1) =>
          localPieceIndex e n))) →
        {n : ℕ // n + 1 < (pieceArc i).1.vertices.length})
    (pieceSource :
      (Sigma (fun e : Fin E.length =>
        Sigma (fun n : Fin ((E[e.1]'e.2).1.vertices.length - 1) =>
          localPieceIndex e n))) → EuclideanSpace ℝ (Fin 2))
    (pieceTarget :
      (Sigma (fun e : Fin E.length =>
        Sigma (fun n : Fin ((E[e.1]'e.2).1.vertices.length - 1) =>
          localPieceIndex e n))) → EuclideanSpace ℝ (Fin 2))
    (pieceArc_eq :
      ∀ i : Sigma (fun e : Fin E.length =>
        Sigma (fun n : Fin ((E[e.1]'e.2).1.vertices.length - 1) =>
          localPieceIndex e n)),
        pieceArc i = E[i.1.1]'i.1.2)
    (pieceSegmentIndex_eq :
      ∀ i : Sigma (fun e : Fin E.length =>
        Sigma (fun n : Fin ((E[e.1]'e.2).1.vertices.length - 1) =>
          localPieceIndex e n)),
        (pieceSegmentIndex i).1 = i.2.1.1)
    (pieceSource_eq_global :
      ∀ i : Sigma (fun e : Fin E.length =>
        Sigma (fun n : Fin ((E[e.1]'e.2).1.vertices.length - 1) =>
          localPieceIndex e n)),
        pieceSource i =
          AffineMap.lineMap
            ((E[i.1.1]'i.1.2).1.vertices[i.2.1.1]'
              (Nat.lt_of_succ_lt (segmentIndex_lt i.1 i.2.1)))
            ((E[i.1.1]'i.1.2).1.vertices[i.2.1.1 + 1]'
              (segmentIndex_lt i.1 i.2.1))
            (pieceSourceParam i).1)
    (pieceTarget_eq_global :
      ∀ i : Sigma (fun e : Fin E.length =>
        Sigma (fun n : Fin ((E[e.1]'e.2).1.vertices.length - 1) =>
          localPieceIndex e n)),
        pieceTarget i =
          AffineMap.lineMap
            ((E[i.1.1]'i.1.2).1.vertices[i.2.1.1]'
              (Nat.lt_of_succ_lt (segmentIndex_lt i.1 i.2.1)))
            ((E[i.1.1]'i.1.2).1.vertices[i.2.1.1 + 1]'
              (segmentIndex_lt i.1 i.2.1))
            (pieceTargetParam i).1)
    (pieceSource_eq_arc :
      ∀ i : Sigma (fun e : Fin E.length =>
        Sigma (fun n : Fin ((E[e.1]'e.2).1.vertices.length - 1) =>
          localPieceIndex e n)),
        pieceSource i =
          AffineMap.lineMap
            ((pieceArc i).1.vertices[(pieceSegmentIndex i).1]'
              (Nat.lt_of_succ_lt (pieceSegmentIndex i).2))
            ((pieceArc i).1.vertices[(pieceSegmentIndex i).1 + 1]'
              (pieceSegmentIndex i).2)
            (pieceSourceParam i).1)
    (pieceTarget_eq_arc :
      ∀ i : Sigma (fun e : Fin E.length =>
        Sigma (fun n : Fin ((E[e.1]'e.2).1.vertices.length - 1) =>
          localPieceIndex e n)),
        pieceTarget i =
          AffineMap.lineMap
            ((pieceArc i).1.vertices[(pieceSegmentIndex i).1]'
              (Nat.lt_of_succ_lt (pieceSegmentIndex i).2))
            ((pieceArc i).1.vertices[(pieceSegmentIndex i).1 + 1]'
              (pieceSegmentIndex i).2)
            (pieceTargetParam i).1) :
    let PieceIndex : Type :=
      Sigma (fun e : Fin E.length =>
        Sigma (fun n : Fin ((E[e.1]'e.2).1.vertices.length - 1) =>
          localPieceIndex e n))
    let OrderIndex : Type :=
      Sigma (fun e : Fin E.length =>
        Sigma (fun n : Fin ((E[e.1]'e.2).1.vertices.length - 1) =>
          Fin ((cutList e n).length - 1)))
    let orderIndexList : List OrderIndex :=
      (List.finRange E.length).sigma fun e =>
        (List.finRange ((E[e.1]'e.2).1.vertices.length - 1)).sigma fun n =>
          List.finRange ((cutList e n).length - 1)
    ∃ (pieceAt : OrderIndex → PieceIndex) (pieceStream : List PieceIndex),
      orderIndexList.Nodup ∧
        (∀ o : OrderIndex, o ∈ orderIndexList) ∧
          (∀ o : OrderIndex, (pieceAt o).1 = o.1) ∧
            (∀ o : OrderIndex, (pieceAt o).2.1.1 = o.2.1.1) ∧
              (∀ o : OrderIndex, pieceNumber (pieceAt o) = o.2.2.1) ∧
                Function.Injective pieceAt ∧
                  pieceStream = orderIndexList.map pieceAt ∧
                    pieceStream.Nodup ∧
                      (∀ i : PieceIndex, i ∈ pieceStream) ∧
                        0 < pieceStream.length ∧
                          (∀ n (hn : n + 1 < pieceStream.length),
                            pieceTarget pieceStream[n] = pieceSource pieceStream[n + 1]) ∧
                            (∀ i, pieceStream.getLast? = some i →
                              ∀ j, pieceStream.head? = some j →
                                pieceTarget i = pieceSource j) ∧
                              ∃ sourceOccurrenceList :
                                  List {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points},
                                sourceOccurrenceList =
                                  List.flatMap (fun i =>
                                    if h : pieceSource i ∈ K.points then
                                      [(⟨pieceSource i, h⟩ :
                                        {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points})]
                                    else [])
                                    pieceStream ∧
                                  sourceOccurrenceList.Nodup ∧
                                    (∀ q, q ∈ sourceOccurrenceList → q.1 ∈ K.points) ∧
                                      (∀ p : {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points},
                                        p ∈ sourceOccurrenceList) ∧
                                        (∀ q, q ∈ sourceOccurrenceList →
                                          ∃ i, i ∈ pieceStream ∧ q.1 = pieceSource i) ∧
                                          (∀ q, q ∈ sourceOccurrenceList →
                                            ∃ n, ∃ hn : n < pieceStream.length,
                                              q.1 = pieceSource pieceStream[n] ∧
                                                ((n = 0 ∧
                                                    ∀ i, pieceStream.getLast? = some i →
                                                      pieceTarget i = q.1) ∨
                                                  (0 < n ∧
                                                    pieceTarget pieceStream[n - 1] = q.1))) := by
  classical
  intro PieceIndex OrderIndex orderIndexList
  rcases
    FinitePolygonalSetCyclicGlobalPieceStreamEnumeration
      J K E cutList localPieceIndex pieceNumber pieceNumber_lt
      pieceNumber_surjective pieceNumber_injective pieceSourceParam
      pieceTargetParam pieceSourceParam_eq pieceTargetParam_eq with
    ⟨pieceAt, pieceStream, horder_nodup, horder_mem, hpieceAt_edge,
      hpieceAt_segment, hpieceAt_number, hpieceAt_injective, hstream_eq,
      hstream_nodup, hstream_mem, _hadjacent_params⟩
  rcases
    FinitePolygonalSetCyclicActualStreamEndpointContinuityBridge
      J K E hEpos hEsucc hEwrap cutList cutList_sorted cutList_zero
      cutList_one cutList_bounds localPieceIndex pieceNumber pieceNumber_lt
      pieceSourceParam pieceTargetParam pieceSourceParam_eq pieceTargetParam_eq
      pieceArc pieceSegmentIndex pieceSource pieceTarget pieceArc_eq
      pieceSegmentIndex_eq pieceSource_eq_arc pieceTarget_eq_arc pieceAt
      pieceStream hpieceAt_edge hpieceAt_segment hpieceAt_number hstream_eq with
    ⟨hstream_pos, hconsecutive, hcyclic_consecutive⟩
  have hadjacent :
      ∀ n (hn : n + 1 < pieceStream.length),
        pieceTarget pieceStream[n] = pieceSource pieceStream[n + 1] := by
    intro n hn
    exact (hconsecutive n hn).1
  have hcyclic :
      ∀ i, pieceStream.getLast? = some i →
        ∀ j, pieceStream.head? = some j → pieceTarget i = pieceSource j := by
    intro i hi j hj
    exact (hcyclic_consecutive i hi j hj).1
  rcases
    FinitePolygonalSetCyclicUnnormalizedListedPointOccurrences
      J K hKJ E hEall segmentIndex_lt cutList cutList_sorted cutList_mem
      cutList_zero cutList_one cutList_bounds localPieceIndex pieceNumber
      pieceNumber_lt pieceNumber_surjective pieceSourceParam pieceTargetParam
      pieceSourceParam_eq pieceTargetParam_eq pieceSource pieceTarget
      pieceSource_eq_global pieceTarget_eq_global pieceStream hstream_mem with
    ⟨rawOccurrenceList, hraw_eq, _hraw_listed, hraw_covers⟩
  rcases
    FinitePolygonalSetCyclicSourceOccurrenceCollapse
      K pieceStream pieceSource pieceTarget hstream_pos hadjacent hcyclic
      rawOccurrenceList hraw_eq hraw_covers with
    ⟨sourceOccurrenceList, hsource_eq, hsource_listed, hsource_covers,
      hsource_cert, hsource_boundary⟩
  have hsource_separation :
      ∀ i j : PieceIndex, pieceSource i = pieceSource j → i = j := by
    exact
      FinitePolygonalSetCyclicGlobalSourceSeparation
        J E hEnodup segmentIndex_lt cutList cutList_nodup cutList_bounds
        localPieceIndex pieceNumber pieceNumber_lt pieceNumber_injective
        pieceSourceParam pieceTargetParam pieceSourceParam_lt
        pieceSourceParam_eq pieceTargetParam_eq pieceSource pieceSource_eq_global
  have hsource_flat_nodup :
      (List.flatMap (fun i =>
        if h : pieceSource i ∈ K.points then
          [(⟨pieceSource i, h⟩ :
            {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points})]
        else [])
        pieceStream).Nodup := by
    let sourceOption :
        PieceIndex → Option {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points} :=
      fun i => if h : pieceSource i ∈ K.points then some ⟨pieceSource i, h⟩ else none
    have hfilter : (List.filterMap sourceOption pieceStream).Nodup := by
      exact hstream_nodup.filterMap (by
        intro a a' b hb hb'
        dsimp [sourceOption] at hb hb'
        by_cases ha : pieceSource a ∈ K.points
        · simp [ha] at hb
          by_cases ha' : pieceSource a' ∈ K.points
          · simp [ha'] at hb'
            have hsub :
                (⟨pieceSource a, ha⟩ :
                  {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points}) =
                  (⟨pieceSource a', ha'⟩ :
                    {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points}) := by
              exact hb.trans hb'.symm
            exact hsource_separation a a' (congrArg Subtype.val hsub)
          · simp [ha'] at hb'
        · simp [ha] at hb)
    rw [List.filterMap_eq_flatMap_toList] at hfilter
    have hfun :
        (fun a => (sourceOption a).toList) =
          (fun i =>
            if h : pieceSource i ∈ K.points then
              [(⟨pieceSource i, h⟩ :
                {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points})]
            else []) := by
      funext i
      by_cases h : pieceSource i ∈ K.points
      · simp [sourceOption, h]
      · simp [sourceOption, h]
    simpa [hfun] using hfilter
  have hsource_nodup : sourceOccurrenceList.Nodup := by
    rw [hsource_eq]
    exact hsource_flat_nodup
  refine ⟨pieceAt, pieceStream, horder_nodup, horder_mem, hpieceAt_edge,
    hpieceAt_segment, hpieceAt_number, hpieceAt_injective, hstream_eq,
    hstream_nodup, hstream_mem, hstream_pos, hadjacent, hcyclic, ?_⟩
  exact ⟨sourceOccurrenceList, hsource_eq, hsource_nodup, hsource_listed,
    hsource_covers, hsource_cert, hsource_boundary⟩
