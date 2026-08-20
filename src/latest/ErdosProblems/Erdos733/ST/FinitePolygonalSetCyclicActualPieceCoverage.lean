import ErdosProblems.Erdos733.ST.FinitePolygonalSetCyclicGlobalElementaryPieceSkeleton
import ErdosProblems.Erdos733.ST.FinitePolygonalSetCyclicActualNormalizedSourceCycle
import ErdosProblems.Erdos733.ST.FinitePolygonalSetCyclicActualStreamIntervalBlocks
import ErdosProblems.Erdos733.ST.FiniteSortedRealCutListCoversUnitInterval
import Mathlib.Tactic

open Classical
noncomputable section

lemma FinitePolygonalSetCyclicActualSourceEqStart
    (K : FinitePolygonalSet) {PieceIndex : Type}
    (pieceSource : PieceIndex → EuclideanSpace ℝ (Fin 2))
    (arcPieceOrder :
      {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points} → List PieceIndex)
    (arcPieceOrder_nonempty :
      ∀ p : {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points},
        (arcPieceOrder p).length ≠ 0)
    (arcPieceOrder_head_source :
      ∀ (p : {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points}) i,
        (arcPieceOrder p).head? = some i → pieceSource i = p.1)
    (arcPieceOrder_tail_no_source :
      ∀ (p : {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points}) i,
        i ∈ (arcPieceOrder p).tail → pieceSource i ∉ K.points) :
    ∀ (p : {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points}) i,
      i ∈ arcPieceOrder p → pieceSource i ∈ K.points →
        pieceSource i = p.1 := by
  intro p i hi hlisted
  cases hL : arcPieceOrder p with
  | nil =>
      have hlen : (arcPieceOrder p).length = 0 := by simp [hL]
      exact False.elim (arcPieceOrder_nonempty p hlen)
  | cons a tail =>
      simp only [hL, List.mem_cons] at hi
      rcases hi with hi_eq | htail
      · subst i
        have hhead : (arcPieceOrder p).head? = some a := by simp [hL]
        exact arcPieceOrder_head_source p a hhead
      · exact False.elim
          ((arcPieceOrder_tail_no_source p i (by simpa [hL] using htail))
            hlisted)

lemma FinitePolygonalSetCyclicActualTargetEqSuccessor
    (K : FinitePolygonalSet) {PieceIndex : Type}
    (successor : Equiv.Perm
      {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points})
    (pieceSource pieceTarget : PieceIndex → EuclideanSpace ℝ (Fin 2))
    (arcPieceOrder :
      {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points} → List PieceIndex)
    (arcPieceOrder_last_target :
      ∀ (p : {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points}) i,
        (arcPieceOrder p).getLast? = some i →
          pieceTarget i = (successor p).1)
    (arcPieceOrder_consecutive_endpoint :
      ∀ (p : {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points})
        n (hn : n + 1 < (arcPieceOrder p).length),
        pieceTarget ((arcPieceOrder p)[n]) =
          pieceSource ((arcPieceOrder p)[n + 1]))
    (arcPieceOrder_tail_no_source :
      ∀ (p : {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points}) i,
        i ∈ (arcPieceOrder p).tail → pieceSource i ∉ K.points) :
    ∀ (p : {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points}) i,
      i ∈ arcPieceOrder p → pieceTarget i ∈ K.points →
        pieceTarget i = (successor p).1 := by
  intro p i hi hlisted
  rcases List.getElem_of_mem hi with ⟨n, hn, hget⟩
  by_cases hlast_index : n + 1 = (arcPieceOrder p).length
  · have hlast_lt : (arcPieceOrder p).length - 1 < (arcPieceOrder p).length := by
      omega
    have hn_eq : n = (arcPieceOrder p).length - 1 := by omega
    have hlast :
        (arcPieceOrder p).getLast? = some ((arcPieceOrder p)[n]) := by
      rw [List.getLast?_eq_getElem?]
      simp [hn_eq]
    have htarget := arcPieceOrder_last_target p ((arcPieceOrder p)[n]) hlast
    simpa [hget] using htarget
  · have hnnext : n + 1 < (arcPieceOrder p).length := by omega
    let j : PieceIndex := (arcPieceOrder p)[n + 1]
    have hjoin := arcPieceOrder_consecutive_endpoint p n hnnext
    have hj_tail : j ∈ (arcPieceOrder p).tail := by
      have hn_tail : n < (arcPieceOrder p).tail.length := by
        rw [List.length_tail]
        omega
      have htail_get :
          (arcPieceOrder p).tail[n] = (arcPieceOrder p)[n + 1] :=
        List.getElem_tail hn_tail
      simpa [j, htail_get] using
        List.getElem_mem (l := (arcPieceOrder p).tail) (n := n) hn_tail
    have htarget_current :
        pieceTarget ((arcPieceOrder p)[n]) ∈ K.points := by
      simpa [hget] using hlisted
    have hsource_j_listed : pieceSource j ∈ K.points := by
      simpa [j, hjoin] using htarget_current
    exact False.elim
      ((arcPieceOrder_tail_no_source p j hj_tail) hsource_j_listed)

lemma FinitePolygonalSetCyclicActualCarrierCoverage
    (J : SimpleClosedPolygonalCurve)
    (E : List { γ : PolygonalArc // γ ∈ J.edgeArcs })
    (hEall : ∀ γ : { γ : PolygonalArc // γ ∈ J.edgeArcs }, γ ∈ E)
    (segmentIndex_lt :
      (e : Fin E.length) →
        (n : Fin ((E[e.1]'e.2).1.vertices.length - 1)) →
          n.1 + 1 < (E[e.1]'e.2).1.vertices.length)
    (cutList :
      (e : Fin E.length) →
        Fin ((E[e.1]'e.2).1.vertices.length - 1) → List ℝ)
    (cutList_sorted : ∀ e n, (cutList e n).SortedLT)
    (cutList_zero : ∀ e n, (0 : ℝ) ∈ cutList e n)
    (cutList_one : ∀ e n, (1 : ℝ) ∈ cutList e n)
    (cutList_bounds : ∀ e n t, t ∈ cutList e n → 0 ≤ t ∧ t ≤ 1)
    (localPieceIndex :
      (e : Fin E.length) →
        Fin ((E[e.1]'e.2).1.vertices.length - 1) → Type)
    {PieceIndex : Type}
    (pieceOf :
      (e : Fin E.length) →
        (n : Fin ((E[e.1]'e.2).1.vertices.length - 1)) →
          localPieceIndex e n → PieceIndex)
    (pieceNumber : PieceIndex → ℕ)
    (pieceNumber_lt :
      ∀ e n a,
        pieceNumber (pieceOf e n a) + 1 < (cutList e n).length)
    (pieceNumber_surjective :
      ∀ e n k (_hk : k + 1 < (cutList e n).length),
        ∃ a : localPieceIndex e n, pieceNumber (pieceOf e n a) = k)
    (pieceSourceParam pieceTargetParam : PieceIndex → Set.Icc (0 : ℝ) 1)
    (pieceSource pieceTarget : PieceIndex → EuclideanSpace ℝ (Fin 2))
    (pieceCarrier : PieceIndex → Set (EuclideanSpace ℝ (Fin 2)))
    (pieceSourceParam_eq :
      ∀ e n a,
        (pieceSourceParam (pieceOf e n a)).1 =
          (cutList e n)[pieceNumber (pieceOf e n a)]'
            (Nat.lt_of_succ_lt (pieceNumber_lt e n a)))
    (pieceTargetParam_eq :
      ∀ e n a,
        (pieceTargetParam (pieceOf e n a)).1 =
          (cutList e n)[pieceNumber (pieceOf e n a) + 1]'
            (pieceNumber_lt e n a))
    (pieceSource_eq :
      ∀ e n a,
        pieceSource (pieceOf e n a) =
          AffineMap.lineMap
            ((E[e.1]'e.2).1.vertices[n.1]'(Nat.lt_of_succ_lt
              (segmentIndex_lt e n)))
            ((E[e.1]'e.2).1.vertices[n.1 + 1]'(segmentIndex_lt e n))
            (pieceSourceParam (pieceOf e n a)).1)
    (pieceTarget_eq :
      ∀ e n a,
        pieceTarget (pieceOf e n a) =
          AffineMap.lineMap
            ((E[e.1]'e.2).1.vertices[n.1]'(Nat.lt_of_succ_lt
              (segmentIndex_lt e n)))
            ((E[e.1]'e.2).1.vertices[n.1 + 1]'(segmentIndex_lt e n))
            (pieceTargetParam (pieceOf e n a)).1)
    (pieceCarrier_eq :
      ∀ e n a, pieceCarrier (pieceOf e n a) =
        segment ℝ (pieceSource (pieceOf e n a)) (pieceTarget (pieceOf e n a))) :
    J.carrier ⊆ ⋃ i : PieceIndex, pieceCarrier i := by
  intro x hxJ
  rw [J.carrier_eq] at hxJ
  rcases Set.mem_iUnion.mp hxJ with ⟨γ, hxγ⟩
  rw [γ.1.carrier_eq] at hxγ
  rcases hxγ with ⟨m, hm, hxseg⟩
  rcases List.getElem_of_mem (hEall γ) with ⟨r, hr, hEr⟩
  let e : Fin E.length := ⟨r, hr⟩
  have hmE : m + 1 < (E[e.1]'e.2).1.vertices.length := by
    simpa [e, hEr] using hm
  let n : Fin ((E[e.1]'e.2).1.vertices.length - 1) := ⟨m, by omega⟩
  let A : EuclideanSpace ℝ (Fin 2) :=
    (E[e.1]'e.2).1.vertices[n.1]'(Nat.lt_of_succ_lt (segmentIndex_lt e n))
  let B : EuclideanSpace ℝ (Fin 2) :=
    (E[e.1]'e.2).1.vertices[n.1 + 1]'(segmentIndex_lt e n)
  have hxsegE : x ∈ segment ℝ A B := by
    simpa [A, B, e, n, hEr] using hxseg
  rw [segment_eq_image_lineMap] at hxsegE
  rcases hxsegE with ⟨t, ht, htx⟩
  rcases
    FiniteSortedRealCutListCoversUnitInterval (cutList e n)
      (cutList_sorted e n) (cutList_zero e n) (cutList_one e n)
      (cutList_bounds e n) t ht with
    ⟨k, hk, htk⟩
  rcases pieceNumber_surjective e n k hk with ⟨a, ha⟩
  let i : PieceIndex := pieceOf e n a
  refine Set.mem_iUnion.2 ⟨i, ?_⟩
  have hsrcParam :
      (pieceSourceParam i).1 =
        (cutList e n)[k]'(Nat.lt_of_succ_lt hk) := by
    simpa [i, ha] using pieceSourceParam_eq e n a
  have htgtParam :
      (pieceTargetParam i).1 = (cutList e n)[k + 1]'hk := by
    simpa [i, ha] using pieceTargetParam_eq e n a
  rw [pieceCarrier_eq e n a, pieceSource_eq e n a, pieceTarget_eq e n a,
    hsrcParam, htgtParam]
  change x ∈
    segment ℝ
      (AffineMap.lineMap A B ((cutList e n)[k]'(Nat.lt_of_succ_lt hk)))
      (AffineMap.lineMap A B ((cutList e n)[k + 1]'hk))
  rw [← image_segment ℝ (AffineMap.lineMap A B)
    ((cutList e n)[k]'(Nat.lt_of_succ_lt hk)) ((cutList e n)[k + 1]'hk)]
  exact ⟨t, htk, htx⟩


-- [TABLET NODE: FinitePolygonalSetCyclicActualPieceCoverage]
lemma FinitePolygonalSetCyclicActualPieceCoverage
    (J : SimpleClosedPolygonalCurve) (K : FinitePolygonalSet)
    (hKJ : K.carrier = J.carrier) :
    ∃ (PieceIndex : Type) (_pieceIndex_fintype : Fintype PieceIndex)
      (successor : Equiv.Perm {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points})
      (pieceArc : PieceIndex → {γ : PolygonalArc // γ ∈ J.edgeArcs})
      (pieceSegmentIndex :
        (i : PieceIndex) → {n : ℕ // n + 1 < (pieceArc i).1.vertices.length})
      (pieceSource pieceTarget : PieceIndex → EuclideanSpace ℝ (Fin 2))
      (pieceSourceParam pieceTargetParam : PieceIndex → Set.Icc (0 : ℝ) 1)
      (pieceCarrier : PieceIndex → Set (EuclideanSpace ℝ (Fin 2)))
      (arcPieceOrder :
        {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points} → List PieceIndex),
        (∀ i, pieceSourceParam i < pieceTargetParam i) ∧
          (∀ i,
            pieceSource i =
              AffineMap.lineMap
                ((pieceArc i).1.vertices[(pieceSegmentIndex i).1]'
                  (Nat.lt_of_succ_lt (pieceSegmentIndex i).2))
                ((pieceArc i).1.vertices[(pieceSegmentIndex i).1 + 1]'
                  (pieceSegmentIndex i).2)
                (pieceSourceParam i).1) ∧
          (∀ i,
            pieceTarget i =
              AffineMap.lineMap
                ((pieceArc i).1.vertices[(pieceSegmentIndex i).1]'
                  (Nat.lt_of_succ_lt (pieceSegmentIndex i).2))
                ((pieceArc i).1.vertices[(pieceSegmentIndex i).1 + 1]'
                  (pieceSegmentIndex i).2)
                (pieceTargetParam i).1) ∧
          (∀ i, pieceCarrier i = segment ℝ (pieceSource i) (pieceTarget i)) ∧
          (∀ i (v : EuclideanSpace ℝ (Fin 2)),
            v ∈ K.points → v ∉ openSegment ℝ (pieceSource i) (pieceTarget i)) ∧
          (∀ p : {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points},
            (arcPieceOrder p).length ≠ 0) ∧
          (∀ (p : {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points}) i,
            (arcPieceOrder p).head? = some i → pieceSource i = p.1) ∧
          (∀ (p : {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points}) i,
            (arcPieceOrder p).getLast? = some i →
              pieceTarget i = (successor p).1) ∧
          (∀ (p : {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points})
            n (hn : n + 1 < (arcPieceOrder p).length),
            pieceTarget ((arcPieceOrder p)[n]) =
                pieceSource ((arcPieceOrder p)[n + 1]) ∧
              ((pieceArc ((arcPieceOrder p)[n]) =
                    pieceArc ((arcPieceOrder p)[n + 1]) ∧
                  (pieceSegmentIndex ((arcPieceOrder p)[n])).1 =
                    (pieceSegmentIndex ((arcPieceOrder p)[n + 1])).1 ∧
                  pieceTargetParam ((arcPieceOrder p)[n]) =
                    pieceSourceParam ((arcPieceOrder p)[n + 1])) ∨
                (pieceArc ((arcPieceOrder p)[n]) =
                    pieceArc ((arcPieceOrder p)[n + 1]) ∧
                  (pieceSegmentIndex ((arcPieceOrder p)[n])).1 + 1 =
                    (pieceSegmentIndex ((arcPieceOrder p)[n + 1])).1 ∧
                  (pieceTargetParam ((arcPieceOrder p)[n])).1 = 1 ∧
                  (pieceSourceParam ((arcPieceOrder p)[n + 1])).1 = 0) ∨
                (pieceArc ((arcPieceOrder p)[n + 1]) =
                    J.successor (pieceArc ((arcPieceOrder p)[n])) ∧
                  (pieceSegmentIndex ((arcPieceOrder p)[n])).1 + 2 =
                    (pieceArc ((arcPieceOrder p)[n])).1.vertices.length ∧
                  (pieceSegmentIndex ((arcPieceOrder p)[n + 1])).1 = 0 ∧
                  (pieceTargetParam ((arcPieceOrder p)[n])).1 = 1 ∧
                  (pieceSourceParam ((arcPieceOrder p)[n + 1])).1 = 0))) ∧
          (∀ (p : {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points}) i,
            i ∈ (arcPieceOrder p).tail → pieceSource i ∉ K.points) ∧
          (∀ (p : {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points}) i,
            i ∈ arcPieceOrder p → pieceSource i ∈ K.points →
              pieceSource i = p.1) ∧
          (∀ (p : {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points}) i,
            i ∈ arcPieceOrder p → pieceTarget i ∈ K.points →
              pieceTarget i = (successor p).1) ∧
          (∀ p q : {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points},
            ∃ n : ℕ, (successor^[n]) p = q) ∧
          (∀ p : {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points},
            p.1 ≠ (successor p).1) ∧
          J.carrier ⊆ ⋃ i : PieceIndex, pieceCarrier i := by
-- BODY
  classical
  rcases FinitePolygonalSetCyclicGlobalElementaryPieceSkeleton J K with
    ⟨E, hEnodup, hEall, hEpos, hEsucc, hEwrap,
      segmentIndex_lt, cutList, cutList_nodup, cutList_sorted, cutList_mem,
      cutList_zero, cutList_one, cutList_bounds, cutList_lt,
      localPieceIndex, localPieceFintype, pieceIndexFintype,
      pieceNumber, pieceNumber_lt, pieceEdgePosition, pieceArc,
      pieceSegmentIndexRaw, pieceSourceParam, pieceTargetParam, pieceSource,
      pieceTarget, pieceCarrier, pieceEdgePosition_eq, pieceArc_eq_raw,
      pieceSegmentIndexRaw_eq, pieceNumber_surjective, pieceNumber_injective,
      pieceSourceParam_lt, pieceSourceParam_eq, pieceTargetParam_eq,
      pieceSource_eq_global, pieceTarget_eq_global, pieceCarrier_eq,
      no_listed_open_piece⟩
  let PieceIndex : Type :=
    Sigma (fun e : Fin E.length =>
      Sigma (fun n : Fin ((E[e.1]'e.2).1.vertices.length - 1) =>
        localPieceIndex e n))
  have pieceArc_eq :
      ∀ i : PieceIndex, pieceArc i = E[i.1.1]'i.1.2 := by
    intro i
    calc
      pieceArc i = E[(pieceEdgePosition i).1]'(pieceEdgePosition i).2 :=
        pieceArc_eq_raw i
      _ = E[i.1.1]'i.1.2 := by
        rw [pieceEdgePosition_eq i]
  let pieceSegmentIndex :
      (i : PieceIndex) → {n : ℕ // n + 1 < (pieceArc i).1.vertices.length} :=
    fun i =>
      ⟨(pieceSegmentIndexRaw i).1, by
        simpa [pieceArc_eq i] using (pieceSegmentIndexRaw i).2⟩
  have pieceSegmentIndex_eq :
      ∀ i : PieceIndex, (pieceSegmentIndex i).1 = i.2.1.1 := by
    intro i
    exact pieceSegmentIndexRaw_eq i
  have pieceSource_eq_arc :
      ∀ i : PieceIndex,
        pieceSource i =
          AffineMap.lineMap
            ((pieceArc i).1.vertices[(pieceSegmentIndex i).1]'
              (Nat.lt_of_succ_lt (pieceSegmentIndex i).2))
            ((pieceArc i).1.vertices[(pieceSegmentIndex i).1 + 1]'
              (pieceSegmentIndex i).2)
            (pieceSourceParam i).1 := by
    intro i
    simpa [pieceSegmentIndex, pieceArc_eq i, pieceSegmentIndexRaw_eq i]
      using pieceSource_eq_global i
  have pieceTarget_eq_arc :
      ∀ i : PieceIndex,
        pieceTarget i =
          AffineMap.lineMap
            ((pieceArc i).1.vertices[(pieceSegmentIndex i).1]'
              (Nat.lt_of_succ_lt (pieceSegmentIndex i).2))
            ((pieceArc i).1.vertices[(pieceSegmentIndex i).1 + 1]'
              (pieceSegmentIndex i).2)
            (pieceTargetParam i).1 := by
    intro i
    simpa [pieceSegmentIndex, pieceArc_eq i, pieceSegmentIndexRaw_eq i]
      using pieceTarget_eq_global i
  rcases
    FinitePolygonalSetCyclicActualNormalizedSourceCycle
      J K hKJ E hEnodup hEall hEpos hEsucc hEwrap segmentIndex_lt
      cutList cutList_nodup cutList_sorted cutList_mem cutList_zero
      cutList_one cutList_bounds localPieceIndex pieceNumber pieceNumber_lt
      pieceNumber_surjective pieceNumber_injective pieceSourceParam
      pieceTargetParam pieceSourceParam_lt pieceSourceParam_eq
      pieceTargetParam_eq pieceArc pieceSegmentIndex pieceSource pieceTarget
      pieceArc_eq pieceSegmentIndex_eq pieceSource_eq_global
      pieceTarget_eq_global pieceSource_eq_arc pieceTarget_eq_arc with
    ⟨pieceAt, pieceStream, horder_nodup, horder_mem, hpieceAt_edge,
      hpieceAt_segment, hpieceAt_number, hpieceAt_injective, hstream_eq,
      hstream_nodup, hstream_mem, hstream_pos, hstream_consecutive_endpoint,
      hstream_cyclic_endpoint, sourceOccurrenceList, hsource_eq,
      hsource_nodup, hsource_listed, hsource_covers, hsource_cert,
      hsource_boundary⟩
  let ConsecutiveOK : PieceIndex → PieceIndex → Prop := fun i j =>
    pieceTarget i = pieceSource j ∧
      ((pieceArc i = pieceArc j ∧
          (pieceSegmentIndex i).1 = (pieceSegmentIndex j).1 ∧
          pieceTargetParam i = pieceSourceParam j) ∨
        (pieceArc i = pieceArc j ∧
          (pieceSegmentIndex i).1 + 1 = (pieceSegmentIndex j).1 ∧
          (pieceTargetParam i).1 = 1 ∧
          (pieceSourceParam j).1 = 0) ∨
        (pieceArc j = J.successor (pieceArc i) ∧
          (pieceSegmentIndex i).1 + 2 = (pieceArc i).1.vertices.length ∧
          (pieceSegmentIndex j).1 = 0 ∧
          (pieceTargetParam i).1 = 1 ∧
          (pieceSourceParam j).1 = 0))
  have hbridge :
      0 < pieceStream.length ∧
        (∀ n (hn : n + 1 < pieceStream.length),
          ConsecutiveOK pieceStream[n] pieceStream[n + 1]) ∧
        (∀ i, pieceStream.getLast? = some i →
          ∀ j, pieceStream.head? = some j → ConsecutiveOK i j) := by
    simpa [ConsecutiveOK] using
      FinitePolygonalSetCyclicActualStreamEndpointContinuityBridge
        J K E hEpos hEsucc hEwrap cutList cutList_sorted cutList_zero
        cutList_one cutList_bounds localPieceIndex pieceNumber pieceNumber_lt
        pieceSourceParam pieceTargetParam pieceSourceParam_eq
        pieceTargetParam_eq pieceArc pieceSegmentIndex pieceSource pieceTarget
        pieceArc_eq pieceSegmentIndex_eq pieceSource_eq_arc
        pieceTarget_eq_arc pieceAt pieceStream hpieceAt_edge
        hpieceAt_segment hpieceAt_number hstream_eq
  rcases hbridge with ⟨_hstream_pos_full, hstream_consecutive, hstream_cyclic⟩
  rcases
    FinitePolygonalSetCyclicActualStreamIntervalBlocks
      J K hKJ pieceStream pieceSource pieceTarget ConsecutiveOK
      (by intro i j h; exact h.1)
      hstream_consecutive hstream_cyclic sourceOccurrenceList hsource_eq
      hsource_nodup hsource_covers with
    ⟨successor, hsuccessor_eq, hsuccessor_cycle, hsuccessor_nondeg,
      hblocks⟩
  choose arcPieceOrder arcPieceOrder_nonempty arcPieceOrder_head_source
    arcPieceOrder_last_target arcPieceOrder_chain arcPieceOrder_tail_no_source
    arcPieceOrder_mem_stream arcPieceOrder_cases using hblocks
  have arcPieceOrder_consecutive_ok :
      ∀ (p : {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points})
        n (hn : n + 1 < (arcPieceOrder p).length),
        ConsecutiveOK (arcPieceOrder p)[n] (arcPieceOrder p)[n + 1] := by
    intro p n hn
    exact List.isChain_iff_getElem.mp (arcPieceOrder_chain p) n hn
  have pieceSource_listed_eq_start :
      ∀ (p : {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points}) i,
        i ∈ arcPieceOrder p → pieceSource i ∈ K.points →
          pieceSource i = p.1 := by
    exact
      FinitePolygonalSetCyclicActualSourceEqStart K pieceSource arcPieceOrder
        arcPieceOrder_nonempty arcPieceOrder_head_source
        arcPieceOrder_tail_no_source
  have pieceTarget_listed_eq_target :
      ∀ (p : {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points}) i,
        i ∈ arcPieceOrder p → pieceTarget i ∈ K.points →
          pieceTarget i = (successor p).1 := by
    exact
      FinitePolygonalSetCyclicActualTargetEqSuccessor K successor pieceSource
        pieceTarget arcPieceOrder arcPieceOrder_last_target
        (fun p n hn => (arcPieceOrder_consecutive_ok p n hn).1)
        arcPieceOrder_tail_no_source
  have hpieceCarrier_covers_curve :
      J.carrier ⊆ ⋃ i : PieceIndex, pieceCarrier i := by
    apply
      FinitePolygonalSetCyclicActualCarrierCoverage J E hEall
        segmentIndex_lt cutList cutList_sorted cutList_zero cutList_one
        cutList_bounds localPieceIndex
        (fun e n a => (⟨e, ⟨n, a⟩⟩ : PieceIndex)) pieceNumber
        (fun e n a => pieceNumber_lt (⟨e, ⟨n, a⟩⟩ : PieceIndex))
        pieceNumber_surjective pieceSourceParam pieceTargetParam pieceSource
        pieceTarget pieceCarrier
    · intro e n a
      exact pieceSourceParam_eq (⟨e, ⟨n, a⟩⟩ : PieceIndex)
    · intro e n a
      exact pieceTargetParam_eq (⟨e, ⟨n, a⟩⟩ : PieceIndex)
    · intro e n a
      exact pieceSource_eq_global (⟨e, ⟨n, a⟩⟩ : PieceIndex)
    · intro e n a
      exact pieceTarget_eq_global (⟨e, ⟨n, a⟩⟩ : PieceIndex)
    · intro e n a
      exact pieceCarrier_eq (⟨e, ⟨n, a⟩⟩ : PieceIndex)
  refine
    ⟨PieceIndex, pieceIndexFintype, successor, pieceArc, pieceSegmentIndex,
      pieceSource, pieceTarget, pieceSourceParam, pieceTargetParam,
      pieceCarrier, arcPieceOrder, pieceSourceParam_lt, pieceSource_eq_arc,
      pieceTarget_eq_arc, pieceCarrier_eq, no_listed_open_piece,
      arcPieceOrder_nonempty, arcPieceOrder_head_source,
      arcPieceOrder_last_target, (by
        intro p n hn
        simpa only [ConsecutiveOK] using
          arcPieceOrder_consecutive_ok p n hn),
      arcPieceOrder_tail_no_source, pieceSource_listed_eq_start,
      pieceTarget_listed_eq_target, hsuccessor_cycle, hsuccessor_nondeg,
      hpieceCarrier_covers_curve⟩
