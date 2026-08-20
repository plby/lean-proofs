import ErdosProblems.Erdos733.ST.FinitePolygonalSetCyclicActualStreamAdjacencyBridge

open Classical
noncomputable section

-- [TABLET NODE: FinitePolygonalSetCyclicActualStreamEndpointContinuityBridge]
lemma FinitePolygonalSetCyclicActualStreamEndpointContinuityBridge
    (J : SimpleClosedPolygonalCurve) (K : FinitePolygonalSet)
    (E : List {γ : PolygonalArc // γ ∈ J.edgeArcs})
    (hEpos : 0 < E.length)
    (hEsucc : ∀ n (hn : n + 1 < E.length),
      J.successor (E[n]) = E[n + 1])
    (hEwrap : ∀ (hLast : E.length - 1 < E.length) (hFirst : 0 < E.length),
      J.successor (E[E.length - 1]'hLast) = E[0]'hFirst)
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
    (pieceNumber :
      (Sigma (fun e : Fin E.length =>
        Sigma (fun n : Fin ((E[e.1]'e.2).1.vertices.length - 1) =>
          localPieceIndex e n))) → ℕ)
    (pieceNumber_lt :
      ∀ i : Sigma (fun e : Fin E.length =>
        Sigma (fun n : Fin ((E[e.1]'e.2).1.vertices.length - 1) =>
          localPieceIndex e n)),
        pieceNumber i + 1 < (cutList i.1 i.2.1).length)
    (pieceSourceParam :
      (Sigma (fun e : Fin E.length =>
        Sigma (fun n : Fin ((E[e.1]'e.2).1.vertices.length - 1) =>
          localPieceIndex e n))) → Set.Icc (0 : ℝ) 1)
    (pieceTargetParam :
      (Sigma (fun e : Fin E.length =>
        Sigma (fun n : Fin ((E[e.1]'e.2).1.vertices.length - 1) =>
          localPieceIndex e n))) → Set.Icc (0 : ℝ) 1)
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
          localPieceIndex e n))) →
        EuclideanSpace ℝ (Fin 2))
    (pieceTarget :
      (Sigma (fun e : Fin E.length =>
        Sigma (fun n : Fin ((E[e.1]'e.2).1.vertices.length - 1) =>
          localPieceIndex e n))) →
        EuclideanSpace ℝ (Fin 2))
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
    (pieceSource_eq :
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
    (pieceTarget_eq :
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
    ∀ (pieceAt : OrderIndex → PieceIndex) (pieceStream : List PieceIndex),
      (∀ o : OrderIndex, (pieceAt o).1 = o.1) →
      (∀ o : OrderIndex, (pieceAt o).2.1.1 = o.2.1.1) →
      (∀ o : OrderIndex, pieceNumber (pieceAt o) = o.2.2.1) →
      pieceStream = orderIndexList.map pieceAt →
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
              (pieceSegmentIndex i).1 + 2 =
                (pieceArc i).1.vertices.length ∧
              (pieceSegmentIndex j).1 = 0 ∧
              (pieceTargetParam i).1 = 1 ∧
              (pieceSourceParam j).1 = 0))
      0 < pieceStream.length ∧
        (∀ n (hn : n + 1 < pieceStream.length),
          ConsecutiveOK pieceStream[n] pieceStream[n + 1]) ∧
        (∀ i, pieceStream.getLast? = some i →
          ∀ j, pieceStream.head? = some j → ConsecutiveOK i j) := by
-- BODY
  classical
  intro PieceIndex OrderIndex orderIndexList pieceAt pieceStream
    pieceAt_edge pieceAt_segment pieceAt_number hstream ConsecutiveOK
  let TransitionOK : PieceIndex → PieceIndex → Prop := fun i j =>
    ((i.1 = j.1 ∧
        i.2.1.1 = j.2.1.1 ∧
        pieceTargetParam i = pieceSourceParam j) ∨
      (i.1 = j.1 ∧
        i.2.1.1 + 1 = j.2.1.1 ∧
        (pieceTargetParam i).1 = 1 ∧
        (pieceSourceParam j).1 = 0) ∨
      (E[j.1.1]'j.1.2 = J.successor (E[i.1.1]'i.1.2) ∧
        i.2.1.1 + 2 = (E[i.1.1]'i.1.2).1.vertices.length ∧
        j.2.1.1 = 0 ∧
        (pieceTargetParam i).1 = 1 ∧
        (pieceSourceParam j).1 = 0))
  have hbridge :
      0 < pieceStream.length ∧
        (∀ n (hn : n + 1 < pieceStream.length),
          TransitionOK pieceStream[n] pieceStream[n + 1]) ∧
        (∀ i, pieceStream.getLast? = some i →
          ∀ j, pieceStream.head? = some j → TransitionOK i j) := by
    simpa [TransitionOK] using
      FinitePolygonalSetCyclicActualStreamAdjacencyBridge
        J K E hEpos hEsucc hEwrap cutList cutList_sorted cutList_zero
        cutList_one cutList_bounds localPieceIndex pieceNumber pieceNumber_lt
        pieceSourceParam pieceTargetParam pieceSourceParam_eq
        pieceTargetParam_eq pieceAt pieceStream pieceAt_edge pieceAt_segment
        pieceAt_number hstream
  have transition_to_consecutive :
      ∀ i j : PieceIndex, TransitionOK i j → ConsecutiveOK i j := by
    intro i j htrans
    rcases htrans with hsame | hnextOrSucc
    · rcases hsame with ⟨hedge, hseg, hparam⟩
      have harc : pieceArc i = pieceArc j := by
        rw [pieceArc_eq i, pieceArc_eq j, hedge]
      have hseg' :
          (pieceSegmentIndex i).1 = (pieceSegmentIndex j).1 := by
        rw [pieceSegmentIndex_eq i, pieceSegmentIndex_eq j, hseg]
      have hjoin : pieceTarget i = pieceSource j := by
        rw [pieceTarget_eq i, pieceSource_eq j]
        simp [harc, hseg', hparam]
      exact ⟨hjoin, Or.inl ⟨harc, hseg', hparam⟩⟩
    · rcases hnextOrSucc with hnext | hsucc
      · rcases hnext with ⟨hedge, hseg, htarget_one, hsource_zero⟩
        have harc : pieceArc i = pieceArc j := by
          rw [pieceArc_eq i, pieceArc_eq j, hedge]
        have hseg' :
            (pieceSegmentIndex i).1 + 1 = (pieceSegmentIndex j).1 := by
          rw [pieceSegmentIndex_eq i, pieceSegmentIndex_eq j, hseg]
        have hjoin : pieceTarget i = pieceSource j := by
          rw [pieceTarget_eq i, pieceSource_eq j, htarget_one, hsource_zero]
          simp [AffineMap.lineMap_apply_one, AffineMap.lineMap_apply_zero,
            harc, hseg']
        exact ⟨hjoin, Or.inr (Or.inl
          ⟨harc, hseg', htarget_one, hsource_zero⟩)⟩
      · rcases hsucc with
          ⟨hedge, hlast, hzero, htarget_one, hsource_zero⟩
        have harc : pieceArc j = J.successor (pieceArc i) := by
          rw [pieceArc_eq i, pieceArc_eq j]
          exact hedge
        have hlast' :
            (pieceSegmentIndex i).1 + 2 =
              (pieceArc i).1.vertices.length := by
          rw [pieceSegmentIndex_eq i, pieceArc_eq i]
          exact hlast
        have hzero' : (pieceSegmentIndex j).1 = 0 := by
          rw [pieceSegmentIndex_eq j]
          exact hzero
        have htarget_arc : pieceTarget i = (pieceArc i).1.target := by
          let γ : PolygonalArc := (pieceArc i).1
          let m : ℕ := (pieceSegmentIndex i).1
          have hi : m + 1 < γ.vertices.length := by
            simpa [γ, m] using (pieceSegmentIndex i).2
          have htarget_vertex :
              pieceTarget i = γ.vertices[m + 1]'hi := by
            rw [pieceTarget_eq i, htarget_one]
            simp [γ, m]
          have hvertex_target : γ.vertices[m + 1]'hi = γ.target := by
            have hlast_some :
                γ.vertices.getLast? = some (γ.vertices[m + 1]'hi) := by
              rw [List.getLast?_eq_getElem?]
              have hidx : γ.vertices.length - 1 = m + 1 := by
                have hlast'' : m + 2 = γ.vertices.length := by
                  simpa [γ, m] using hlast'
                omega
              simp [hidx]
            exact Option.some.inj (by rw [← hlast_some, γ.target_eq_last])
          exact htarget_vertex.trans hvertex_target
        have hsource_arc : pieceSource j = (pieceArc j).1.source := by
          let δ : PolygonalArc := (pieceArc j).1
          have hj : 0 < δ.vertices.length := by
            have hlen := δ.length_ge_two
            omega
          have hsource_vertex : pieceSource j = δ.vertices[0]'hj := by
            rw [pieceSource_eq j, hsource_zero]
            simp [δ, hzero']
          have hvertex_source : δ.vertices[0]'hj = δ.source := by
            have hhead := δ.source_eq_head
            rw [List.head?_eq_getElem?] at hhead
            rw [List.getElem?_eq_getElem hj] at hhead
            exact Option.some.inj hhead
          exact hsource_vertex.trans hvertex_source
        have hjoin : pieceTarget i = pieceSource j := by
          calc
            pieceTarget i = (pieceArc i).1.target := htarget_arc
            _ = (J.successor (pieceArc i)).1.source :=
              J.adjacent_endpoint (pieceArc i)
            _ = (pieceArc j).1.source := by rw [← harc]
            _ = pieceSource j := hsource_arc.symm
        exact ⟨hjoin, Or.inr (Or.inr
          ⟨harc, hlast', hzero', htarget_one, hsource_zero⟩)⟩
  rcases hbridge with ⟨hpos, hadjacent, hcyclic⟩
  refine ⟨hpos, ?_, ?_⟩
  · intro n hn
    exact transition_to_consecutive pieceStream[n] pieceStream[n + 1]
      (hadjacent n hn)
  · intro i hi j hj
    exact transition_to_consecutive i j (hcyclic i hi j hj)
