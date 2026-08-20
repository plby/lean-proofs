import ErdosProblems.Erdos733.ST.FinitePolygonalSetCyclicGlobalPieceStreamTransitionStep
import Mathlib.Data.List.Chain

open Classical
noncomputable section


-- [TABLET NODE: FinitePolygonalSetCyclicActualStreamAdjacencyBridge]
lemma FinitePolygonalSetCyclicActualStreamAdjacencyBridge
    (J : SimpleClosedPolygonalCurve) (_K : FinitePolygonalSet)
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
            (pieceNumber_lt i)) :
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
      0 < pieceStream.length ∧
        (∀ n (hn : n + 1 < pieceStream.length),
          TransitionOK pieceStream[n] pieceStream[n + 1]) ∧
        (∀ i, pieceStream.getLast? = some i →
          ∀ j, pieceStream.head? = some j → TransitionOK i j) := by
-- BODY
  classical
  intro PieceIndex OrderIndex orderIndexList pieceAt pieceStream
    pieceAt_edge pieceAt_segment pieceAt_number hstream TransitionOK
  let SegmentIndex : Type :=
    Sigma (fun e : Fin E.length =>
      Fin ((E[e.1]'e.2).1.vertices.length - 1))
  let segmentIndexList : List SegmentIndex :=
    (List.finRange E.length).sigma fun e =>
      List.finRange ((E[e.1]'e.2).1.vertices.length - 1)
  let localBlock : SegmentIndex → List PieceIndex := fun s =>
    (List.finRange ((cutList s.1 s.2).length - 1)).map fun k =>
      pieceAt ⟨s.1, ⟨s.2, k⟩⟩
  let pieceBlocks : List (List PieceIndex) := segmentIndexList.map localBlock
  have endpoint_data :
      ∀ e n,
        2 ≤ (cutList e n).length ∧
          (∀ h : 0 < (cutList e n).length,
            (cutList e n)[0]'h = 0) ∧
            (∀ h : (cutList e n).length - 1 < (cutList e n).length,
              (cutList e n)[(cutList e n).length - 1]'h = 1) := by
    intro e n
    exact FiniteSortedRealCutListEndpointEntries
      (cutList e n) (cutList_sorted e n) (cutList_zero e n)
      (cutList_one e n) (cutList_bounds e n)
  have localBlock_ne_nil : ∀ s : SegmentIndex, localBlock s ≠ [] := by
    intro s
    rw [← List.length_pos_iff_ne_nil]
    dsimp [localBlock]
    simp only [List.length_map, List.length_finRange]
    have hlen := (endpoint_data s.1 s.2).1
    omega
  have pieceBlocks_no_nil : [] ∉ pieceBlocks := by
    intro hmem
    rcases List.mem_map.mp hmem with ⟨s, _hs, hs_eq⟩
    exact localBlock_ne_nil s hs_eq
  have target_param_order :
      ∀ (o : OrderIndex),
        (pieceTargetParam (pieceAt o)).1 =
          (cutList o.1 o.2.1)[o.2.2.1 + 1]'(by
            have hk : o.2.2.1 < (cutList o.1 o.2.1).length - 1 := o.2.2.2
            omega) := by
    intro o
    rcases o with ⟨e, n, k⟩
    cases hpiece : pieceAt ⟨e, ⟨n, k⟩⟩ with
    | mk e' rest =>
      cases rest with
      | mk n' a =>
        have he : e' = e := by
          have h := pieceAt_edge ⟨e, ⟨n, k⟩⟩
          rw [hpiece] at h
          exact h
        subst e'
        have hn_val : n'.1 = n.1 := by
          have h := pieceAt_segment ⟨e, ⟨n, k⟩⟩
          rw [hpiece] at h
          exact h
        have hn : n' = n := Fin.ext hn_val
        subst n'
        have hnum : pieceNumber ⟨e, ⟨n, a⟩⟩ = k.1 := by
          have h := pieceAt_number ⟨e, ⟨n, k⟩⟩
          rw [hpiece] at h
          exact h
        have ht := pieceTargetParam_eq (pieceAt ⟨e, ⟨n, k⟩⟩)
        rw [hpiece] at ht
        simpa [hnum] using ht
  have source_param_order :
      ∀ (o : OrderIndex),
        (pieceSourceParam (pieceAt o)).1 =
          (cutList o.1 o.2.1)[o.2.2.1]'(by
            have hk : o.2.2.1 < (cutList o.1 o.2.1).length - 1 := o.2.2.2
            omega) := by
    intro o
    rcases o with ⟨e, n, k⟩
    cases hpiece : pieceAt ⟨e, ⟨n, k⟩⟩ with
    | mk e' rest =>
      cases rest with
      | mk n' a =>
        have he : e' = e := by
          have h := pieceAt_edge ⟨e, ⟨n, k⟩⟩
          rw [hpiece] at h
          exact h
        subst e'
        have hn_val : n'.1 = n.1 := by
          have h := pieceAt_segment ⟨e, ⟨n, k⟩⟩
          rw [hpiece] at h
          exact h
        have hn : n' = n := Fin.ext hn_val
        subst n'
        have hnum : pieceNumber ⟨e, ⟨n, a⟩⟩ = k.1 := by
          have h := pieceAt_number ⟨e, ⟨n, k⟩⟩
          rw [hpiece] at h
          exact h
        have hs := pieceSourceParam_eq (pieceAt ⟨e, ⟨n, k⟩⟩)
        rw [hpiece] at hs
        simpa [hnum] using hs
  have local_same_gap :
      ∀ (e : Fin E.length)
        (n : Fin ((E[e.1]'e.2).1.vertices.length - 1))
        (k kNext : Fin ((cutList e n).length - 1)),
        kNext.1 = k.1 + 1 →
        TransitionOK
          (pieceAt ⟨e, ⟨n, k⟩⟩)
          (pieceAt ⟨e, ⟨n, kNext⟩⟩) := by
    intro e n k kNext hgap
    apply Or.inl
    refine ⟨?_, ?_, ?_⟩
    · rw [pieceAt_edge ⟨e, ⟨n, k⟩⟩, pieceAt_edge ⟨e, ⟨n, kNext⟩⟩]
    · rw [pieceAt_segment ⟨e, ⟨n, k⟩⟩,
        pieceAt_segment ⟨e, ⟨n, kNext⟩⟩]
    · apply Subtype.ext
      have ht := target_param_order ⟨e, ⟨n, k⟩⟩
      have hs := source_param_order ⟨e, ⟨n, kNext⟩⟩
      exact ht.trans (by simpa [hgap] using hs.symm)
  have target_param_last :
      ∀ (o : OrderIndex),
        o.2.2.1 + 1 = (cutList o.1 o.2.1).length - 1 →
        (pieceTargetParam (pieceAt o)).1 = 1 := by
    intro o hlast
    have hlast_lt : (cutList o.1 o.2.1).length - 1 <
        (cutList o.1 o.2.1).length := by
      have hlen := (endpoint_data o.1 o.2.1).1
      omega
    have ht :
        (pieceTargetParam (pieceAt o)).1 =
          (cutList o.1 o.2.1)[(cutList o.1 o.2.1).length - 1]'hlast_lt := by
      simpa [hlast] using target_param_order o
    exact ht.trans ((endpoint_data o.1 o.2.1).2.2 hlast_lt)
  have source_param_first :
      ∀ (o : OrderIndex),
        o.2.2.1 = 0 →
        (pieceSourceParam (pieceAt o)).1 = 0 := by
    intro o hfirst
    have hpos : 0 < (cutList o.1 o.2.1).length := by
      have hlen := (endpoint_data o.1 o.2.1).1
      omega
    have hs :
        (pieceSourceParam (pieceAt o)).1 =
          (cutList o.1 o.2.1)[0]'hpos := by
      simpa [hfirst] using source_param_order o
    exact hs.trans ((endpoint_data o.1 o.2.1).2.1 hpos)
  have local_next_segment :
      ∀ (e : Fin E.length)
        (n nNext : Fin ((E[e.1]'e.2).1.vertices.length - 1))
        (k : Fin ((cutList e n).length - 1))
        (kFirst : Fin ((cutList e nNext).length - 1)),
        n.1 + 1 = nNext.1 →
        k.1 + 1 = (cutList e n).length - 1 →
        kFirst.1 = 0 →
        TransitionOK
          (pieceAt ⟨e, ⟨n, k⟩⟩)
          (pieceAt ⟨e, ⟨nNext, kFirst⟩⟩) := by
    intro e n nNext k kFirst hseg hlast hfirst
    apply Or.inr
    apply Or.inl
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [pieceAt_edge ⟨e, ⟨n, k⟩⟩,
        pieceAt_edge ⟨e, ⟨nNext, kFirst⟩⟩]
    · rw [pieceAt_segment ⟨e, ⟨n, k⟩⟩,
        pieceAt_segment ⟨e, ⟨nNext, kFirst⟩⟩]
      exact hseg
    · exact target_param_last ⟨e, ⟨n, k⟩⟩ hlast
    · exact source_param_first ⟨e, ⟨nNext, kFirst⟩⟩ hfirst
  have local_next_edge :
      ∀ (e eNext : Fin E.length)
        (n : Fin ((E[e.1]'e.2).1.vertices.length - 1))
        (nFirst : Fin ((E[eNext.1]'eNext.2).1.vertices.length - 1))
        (k : Fin ((cutList e n).length - 1))
        (kFirst : Fin ((cutList eNext nFirst).length - 1)),
        E[eNext.1]'eNext.2 = J.successor (E[e.1]'e.2) →
        n.1 + 2 = (E[e.1]'e.2).1.vertices.length →
        nFirst.1 = 0 →
        k.1 + 1 = (cutList e n).length - 1 →
        kFirst.1 = 0 →
        TransitionOK
          (pieceAt ⟨e, ⟨n, k⟩⟩)
          (pieceAt ⟨eNext, ⟨nFirst, kFirst⟩⟩) := by
    intro e eNext n nFirst k kFirst hedge hsegLast hsegFirst hlast hfirst
    apply Or.inr
    apply Or.inr
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · have hi := pieceAt_edge ⟨e, ⟨n, k⟩⟩
      have hj := pieceAt_edge ⟨eNext, ⟨nFirst, kFirst⟩⟩
      rwa [hi, hj]
    · have hs := pieceAt_segment ⟨e, ⟨n, k⟩⟩
      have hlen_eq :
          (E[(pieceAt ⟨e, ⟨n, k⟩⟩).1.1]'(pieceAt ⟨e, ⟨n, k⟩⟩).1.2).1.vertices.length =
            (E[e.1]'e.2).1.vertices.length := by
        simpa [pieceAt_edge ⟨e, ⟨n, k⟩⟩]
      calc
        (pieceAt ⟨e, ⟨n, k⟩⟩).2.1.1 + 2 = n.1 + 2 := by
          rw [hs]
        _ = (E[e.1]'e.2).1.vertices.length := hsegLast
        _ = (E[(pieceAt ⟨e, ⟨n, k⟩⟩).1.1]'(pieceAt ⟨e, ⟨n, k⟩⟩).1.2).1.vertices.length :=
          hlen_eq.symm
    · rw [pieceAt_segment ⟨eNext, ⟨nFirst, kFirst⟩⟩]
      exact hsegFirst
    · exact target_param_last ⟨e, ⟨n, k⟩⟩ hlast
    · exact source_param_first ⟨eNext, ⟨nFirst, kFirst⟩⟩ hfirst
  have localBlock_chain : ∀ s : SegmentIndex, (localBlock s).IsChain TransitionOK := by
    intro s
    dsimp [localBlock]
    rw [List.isChain_map]
    rw [List.isChain_iff_getElem]
    intro m hm
    have hval :
        ((List.finRange ((cutList s.1 s.2).length - 1))[m + 1]).1 =
          ((List.finRange ((cutList s.1 s.2).length - 1))[m]).1 + 1 := by
      simp only [List.length_finRange] at hm
      simp only [List.getElem_finRange, Fin.val_cast]
    exact local_same_gap
      s.1 s.2
      ((List.finRange ((cutList s.1 s.2).length - 1))[m])
      ((List.finRange ((cutList s.1 s.2).length - 1))[m + 1])
      hval
  have pieceBlocks_each_chain : ∀ l ∈ pieceBlocks, l.IsChain TransitionOK := by
    intro l hl
    rcases List.mem_map.mp hl with ⟨s, _hs, rfl⟩
    exact localBlock_chain s
  let SegmentOK : SegmentIndex → SegmentIndex → Prop := fun s t =>
    (s.1 = t.1 ∧ s.2.1 + 1 = t.2.1) ∨
      (E[t.1.1]'t.1.2 = J.successor (E[s.1.1]'s.1.2) ∧
        s.2.1 + 2 = (E[s.1.1]'s.1.2).1.vertices.length ∧
        t.2.1 = 0)
  let edgeSegmentBlock : Fin E.length → List SegmentIndex := fun e =>
    (List.finRange ((E[e.1]'e.2).1.vertices.length - 1)).map fun n =>
      (⟨e, n⟩ : SegmentIndex)
  let segmentBlocks : List (List SegmentIndex) :=
    (List.finRange E.length).map edgeSegmentBlock
  have sigma_eq_flatten :
      ∀ {α : Type} {σ : α → Type} (l : List α) (f : (a : α) → List (σ a)),
        l.sigma f =
          ((l.map fun a => (f a).map fun b => (⟨a, b⟩ : Sigma σ)).flatten) := by
    intro α σ l f
    induction l with
    | nil => simp
    | cons a l ih => simp [ih]
  have segmentIndex_flatten : segmentIndexList = segmentBlocks.flatten := by
    dsimp [segmentIndexList, segmentBlocks, edgeSegmentBlock]
    exact sigma_eq_flatten (List.finRange E.length)
      (fun e => List.finRange ((E[e.1]'e.2).1.vertices.length - 1))
  have edgeSegmentBlock_ne_nil : ∀ e : Fin E.length, edgeSegmentBlock e ≠ [] := by
    intro e
    rw [← List.length_pos_iff_ne_nil]
    dsimp [edgeSegmentBlock]
    simp only [List.length_map, List.length_finRange]
    have hlen : 2 ≤ (E[e.1]'e.2).1.vertices.length :=
      (E[e.1]'e.2).1.length_ge_two
    omega
  have segmentBlocks_no_nil : [] ∉ segmentBlocks := by
    intro hmem
    rcases List.mem_map.mp hmem with ⟨e, _he, heq⟩
    exact edgeSegmentBlock_ne_nil e heq
  have edgeSegmentBlock_chain : ∀ e : Fin E.length, (edgeSegmentBlock e).IsChain SegmentOK := by
    intro e
    dsimp [edgeSegmentBlock, SegmentOK]
    rw [List.isChain_map]
    rw [List.isChain_iff_getElem]
    intro m hm
    apply Or.inl
    refine ⟨rfl, ?_⟩
    simp only [List.length_finRange] at hm
    simp only [List.getElem_finRange, Fin.val_cast]
  have segmentBlocks_each_chain : ∀ l ∈ segmentBlocks, l.IsChain SegmentOK := by
    intro l hl
    rcases List.mem_map.mp hl with ⟨e, _he, rfl⟩
    exact edgeSegmentBlock_chain e
  have edgeSegmentBlock_head :
      ∀ (e : Fin E.length) (x : SegmentIndex),
        x ∈ (edgeSegmentBlock e).head? →
          ∃ n : Fin ((E[e.1]'e.2).1.vertices.length - 1),
            x = ⟨e, n⟩ ∧ n.1 = 0 := by
    intro e x hx
    have hne := edgeSegmentBlock_ne_nil e
    have hhead := List.head?_eq_some_head hne
    rw [hhead] at hx
    have hx_eq : x = (edgeSegmentBlock e).head hne := by
      simpa using hx.symm
    subst x
    let nFirst : Fin ((E[e.1]'e.2).1.vertices.length - 1) :=
      (List.finRange ((E[e.1]'e.2).1.vertices.length - 1))[0]'(by
        rw [List.length_finRange]
        have hlen : 2 ≤ (E[e.1]'e.2).1.vertices.length :=
          (E[e.1]'e.2).1.length_ge_two
        omega)
    refine ⟨nFirst, ?_, ?_⟩
    · dsimp [edgeSegmentBlock, nFirst]
      rw [List.head_eq_getElem_zero]
      simp only [List.length_map, List.length_finRange, List.getElem_map]
    · dsimp [nFirst]
      simp only [List.getElem_finRange, Fin.val_cast]
  have edgeSegmentBlock_last :
      ∀ (e : Fin E.length) (x : SegmentIndex),
        x ∈ (edgeSegmentBlock e).getLast? →
          ∃ n : Fin ((E[e.1]'e.2).1.vertices.length - 1),
            x = ⟨e, n⟩ ∧ n.1 + 2 = (E[e.1]'e.2).1.vertices.length := by
    intro e x hx
    rcases List.mem_getLast?_eq_getLast hx with ⟨hne, rfl⟩
    let segList := List.finRange ((E[e.1]'e.2).1.vertices.length - 1)
    have hsegPos : 0 < segList.length := by
      dsimp [segList]
      simp only [List.length_finRange]
      have hlen : 2 ≤ (E[e.1]'e.2).1.vertices.length :=
        (E[e.1]'e.2).1.length_ge_two
      omega
    let nLast : Fin ((E[e.1]'e.2).1.vertices.length - 1) :=
      segList[segList.length - 1]'(Nat.sub_lt hsegPos Nat.zero_lt_one)
    refine ⟨nLast, ?_, ?_⟩
    · dsimp [edgeSegmentBlock, segList, nLast]
      rw [List.getLast_eq_getElem]
      simp only [List.length_map, List.length_finRange, List.getElem_map,
        List.getElem_finRange]
    · dsimp [segList, nLast]
      simp only [List.length_finRange, List.getElem_finRange, Fin.val_cast]
      have hlen : 2 ≤ (E[e.1]'e.2).1.vertices.length :=
        (E[e.1]'e.2).1.length_ge_two
      omega
  have segmentBlocks_chain :
      segmentBlocks.IsChain
        (fun l₁ l₂ => ∀ x ∈ l₁.getLast?, ∀ y ∈ l₂.head?, SegmentOK x y) := by
    dsimp [segmentBlocks]
    rw [List.isChain_map]
    rw [List.isChain_iff_getElem]
    intro m hm
    intro x hx y hy
    have hnext :
        ((List.finRange E.length)[m + 1]).1 =
          ((List.finRange E.length)[m]).1 + 1 := by
      simp only [List.length_finRange] at hm
      simp only [List.getElem_finRange, Fin.val_cast]
    rcases edgeSegmentBlock_last ((List.finRange E.length)[m]) x hx with
      ⟨nLast, rfl, hnLast⟩
    rcases edgeSegmentBlock_head ((List.finRange E.length)[m + 1]) y hy with
      ⟨nFirst, rfl, hnFirst⟩
    apply Or.inr
    refine ⟨?_, ?_, ?_⟩
    · have hsucc_lt : ((List.finRange E.length)[m]).1 + 1 < E.length := by
        have hlt := ((List.finRange E.length)[m + 1]).2
        omega
      have heq :
          (List.finRange E.length)[m + 1] =
            (⟨((List.finRange E.length)[m]).1 + 1, hsucc_lt⟩ : Fin E.length) :=
        Fin.ext hnext
      exact (congrArg (fun e : Fin E.length => E[e.1]'e.2) heq).trans
        ((hEsucc ((List.finRange E.length)[m]).1 hsucc_lt).symm)
    · exact hnLast
    · exact hnFirst
  have segmentIndexList_chain : segmentIndexList.IsChain SegmentOK := by
    rw [segmentIndex_flatten]
    exact (List.isChain_flatten segmentBlocks_no_nil).2
      ⟨segmentBlocks_each_chain, segmentBlocks_chain⟩
  have localBlock_head :
      ∀ (s : SegmentIndex) (x : PieceIndex),
        x ∈ (localBlock s).head? →
          ∃ k : Fin ((cutList s.1 s.2).length - 1),
            x = pieceAt ⟨s.1, ⟨s.2, k⟩⟩ ∧ k.1 = 0 := by
    intro s x hx
    have hne := localBlock_ne_nil s
    have hhead := List.head?_eq_some_head hne
    rw [hhead] at hx
    have hx_eq : x = (localBlock s).head hne := by
      simpa using hx.symm
    subst x
    let kFirst : Fin ((cutList s.1 s.2).length - 1) :=
      (List.finRange ((cutList s.1 s.2).length - 1))[0]'(by
        rw [List.length_finRange]
        have hlen := (endpoint_data s.1 s.2).1
        omega)
    refine ⟨kFirst, ?_, ?_⟩
    · dsimp [localBlock, kFirst]
      rw [List.head_eq_getElem_zero]
      simp only [List.length_map, List.length_finRange, List.getElem_map]
    · dsimp [kFirst]
      simp only [List.getElem_finRange, Fin.val_cast]
  have localBlock_last :
      ∀ (s : SegmentIndex) (x : PieceIndex),
        x ∈ (localBlock s).getLast? →
          ∃ k : Fin ((cutList s.1 s.2).length - 1),
            x = pieceAt ⟨s.1, ⟨s.2, k⟩⟩ ∧
              k.1 + 1 = (cutList s.1 s.2).length - 1 := by
    intro s x hx
    rcases List.mem_getLast?_eq_getLast hx with ⟨hne, rfl⟩
    let gapList := List.finRange ((cutList s.1 s.2).length - 1)
    have hgapPos : 0 < gapList.length := by
      dsimp [gapList]
      simp only [List.length_finRange]
      have hlen := (endpoint_data s.1 s.2).1
      omega
    let kLast : Fin ((cutList s.1 s.2).length - 1) :=
      gapList[gapList.length - 1]'(Nat.sub_lt hgapPos Nat.zero_lt_one)
    refine ⟨kLast, ?_, ?_⟩
    · dsimp [localBlock, gapList, kLast]
      rw [List.getLast_eq_getElem]
      simp only [List.length_map, List.length_finRange, List.getElem_map]
    · dsimp [gapList, kLast]
      simp only [List.length_finRange, List.getElem_finRange, Fin.val_cast]
      have hlen := (endpoint_data s.1 s.2).1
      omega
  have pieceBlocks_chain :
      pieceBlocks.IsChain
        (fun l₁ l₂ => ∀ x ∈ l₁.getLast?, ∀ y ∈ l₂.head?, TransitionOK x y) := by
    dsimp [pieceBlocks]
    rw [List.isChain_map]
    exact segmentIndexList_chain.imp (by
      intro s t hst
      intro x hx y hy
      rcases localBlock_last s x hx with ⟨kLast, rfl, hkLast⟩
      rcases localBlock_head t y hy with ⟨kFirst, rfl, hkFirst⟩
      rcases hst with hsame | hedge
      · rcases s with ⟨e, n⟩
        rcases t with ⟨e', n'⟩
        dsimp at hsame kLast kFirst hkLast hkFirst
        cases hsame.1
        exact local_next_segment e n n' kLast kFirst
          hsame.2 hkLast hkFirst
      · exact local_next_edge s.1 t.1 s.2 t.2 kLast kFirst
          hedge.1 hedge.2.1 hedge.2.2 hkLast hkFirst)
  have pieceStream_flatten : pieceStream = pieceBlocks.flatten := by
    rw [hstream]
    have sigma_map_flatten :
        ∀ {α β : Type} {σ : α → Type} (l : List α)
          (f : (a : α) → List (σ a)) (g : Sigma σ → β),
          (l.sigma f).map g =
            ((l.map fun a => (f a).map fun b => g ⟨a, b⟩).flatten) := by
      intro α β σ l f g
      induction l with
      | nil => simp
      | cons a l ih => simp [ih]
    have nested_sigma_map_flatten :
        ∀ {α β : Type} {σ : α → Type} {τ : (a : α) → σ a → Type}
          (l : List α) (m : (a : α) → List (σ a))
          (n : (a : α) → (b : σ a) → List (τ a b))
          (g : Sigma (fun a => Sigma (fun b : σ a => τ a b)) → β),
          ((l.sigma fun a => (m a).sigma fun b => n a b).map g) =
            (((l.sigma fun a => m a).map fun ab =>
              (n ab.1 ab.2).map fun c => g ⟨ab.1, ⟨ab.2, c⟩⟩).flatten) := by
      intro α β σ τ l m n g
      induction l with
      | nil => simp
      | cons a l ih =>
        simp [ih, sigma_map_flatten, Function.comp_def]
    dsimp [pieceBlocks, segmentIndexList, localBlock, orderIndexList]
    exact nested_sigma_map_flatten (List.finRange E.length)
      (fun e => List.finRange ((E[e.1]'e.2).1.vertices.length - 1))
      (fun e n => List.finRange ((cutList e n).length - 1))
      pieceAt
  have pieceStream_chain : pieceStream.IsChain TransitionOK := by
    rw [pieceStream_flatten]
    exact (List.isChain_flatten pieceBlocks_no_nil).2
      ⟨pieceBlocks_each_chain, pieceBlocks_chain⟩
  have pieceStream_pos : 0 < pieceStream.length := by
    rw [pieceStream_flatten, List.length_pos_iff_ne_nil]
    rw [List.flatten_ne_nil_iff]
    refine ⟨localBlock ⟨(⟨0, hEpos⟩ : Fin E.length),
      ⟨0, ?_⟩⟩, ?_, ?_⟩
    · exact Nat.sub_pos_of_lt
        ((E[(⟨0, hEpos⟩ : Fin E.length).1]'(⟨0, hEpos⟩ : Fin E.length).2).1.length_ge_two)
    · dsimp [pieceBlocks, segmentIndexList, localBlock]
      rw [List.mem_map]
      refine ⟨(⟨(⟨0, hEpos⟩ : Fin E.length), ⟨0, ?_⟩⟩ : SegmentIndex), ?_, rfl⟩
      · exact Nat.sub_pos_of_lt
          ((E[(⟨0, hEpos⟩ : Fin E.length).1]'(⟨0, hEpos⟩ : Fin E.length).2).1.length_ge_two)
      · rw [List.mem_sigma]
        exact ⟨List.mem_finRange _, List.mem_finRange _⟩
    · apply localBlock_ne_nil
  have map_head?_eq_some :
      ∀ {α β : Type} {l : List α} {a : α} (f : α → β),
        l.head? = some a → (l.map f).head? = some (f a) := by
    intro α β l a f h
    cases l with
    | nil => simp at h
    | cons x xs =>
      simp at h ⊢
      subst a
      rfl
  have map_getLast?_eq_some :
      ∀ {α β : Type} {l : List α} {a : α} (f : α → β),
        l.getLast? = some a → (l.map f).getLast? = some (f a) := by
    intro α β l a f h
    induction l with
    | nil => simp at h
    | cons x xs ih =>
      cases xs with
      | nil =>
        simp at h ⊢
        subst a
        rfl
      | cons y ys =>
        simp at h ⊢
        exact ih h
  have flatten_head?_eq_some :
      ∀ {α : Type} {L : List (List α)} {l : List α} {x : α},
        L.head? = some l → l.head? = some x → L.flatten.head? = some x := by
    intro α L l x hL hl
    cases L with
    | nil => simp at hL
    | cons l0 L =>
      simp at hL
      subst l0
      have hne : l ≠ [] := by
        intro hnil
        simp [hnil] at hl
      simpa [List.head?_append_of_ne_nil _ hne] using hl
  have flatten_getLast?_eq_some :
      ∀ {α : Type} {L : List (List α)} {l : List α} {x : α},
        L.getLast? = some l → l.getLast? = some x → L.flatten.getLast? = some x := by
    intro α L
    induction L with
    | nil =>
      intro l x hL hl
      simp at hL
    | cons a rest ih =>
      intro l x hL hl
      cases rest with
      | nil =>
        simp at hL
        subst a
        simpa using hl
      | cons b bs =>
        have hrest : (b :: bs).getLast? = some l := by
          simpa using hL
        have hflatRest : (b :: bs).flatten.getLast? = some x := ih hrest hl
        have hflatRest_ne : (b :: bs).flatten ≠ [] := by
          intro hnil
          simp [hnil] at hflatRest
        change (a ++ (b :: bs).flatten).getLast? = some x
        rw [List.getLast?_append_of_ne_nil a hflatRest_ne]
        exact hflatRest
  have finRange_head? :
      ∀ (n : ℕ) (h : 0 < n),
        (List.finRange n).head? = some (⟨0, h⟩ : Fin n) := by
    intro n h
    rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by
      simpa [List.length_finRange] using h)]
    apply congrArg some
    apply Fin.ext
    simp only [List.getElem_finRange, Fin.val_cast]
  have finRange_getLast? :
      ∀ (n : ℕ) (h : 0 < n),
        (List.finRange n).getLast? =
          some (⟨n - 1, Nat.sub_lt h Nat.zero_lt_one⟩ : Fin n) := by
    intro n h
    rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by
      simpa [List.length_finRange] using Nat.sub_lt h Nat.zero_lt_one)]
    apply congrArg some
    apply Fin.ext
    simp only [List.length_finRange, List.getElem_finRange, Fin.val_cast]
  refine ⟨pieceStream_pos, ?_, ?_⟩
  · intro n hn
    exact pieceStream_chain.getElem n hn
  · intro i hi j hj
    let eFirst : Fin E.length := ⟨0, hEpos⟩
    have hLastEdge : E.length - 1 < E.length := Nat.sub_lt hEpos Nat.zero_lt_one
    let eLast : Fin E.length := ⟨E.length - 1, hLastEdge⟩
    have hFirstSegPos : 0 < (E[eFirst.1]'eFirst.2).1.vertices.length - 1 :=
      Nat.sub_pos_of_lt (E[eFirst.1]'eFirst.2).1.length_ge_two
    let nFirst : Fin ((E[eFirst.1]'eFirst.2).1.vertices.length - 1) :=
      ⟨0, hFirstSegPos⟩
    have hLastSegCountPos : 0 < (E[eLast.1]'eLast.2).1.vertices.length - 1 :=
      Nat.sub_pos_of_lt (E[eLast.1]'eLast.2).1.length_ge_two
    let nLast : Fin ((E[eLast.1]'eLast.2).1.vertices.length - 1) :=
      ⟨(E[eLast.1]'eLast.2).1.vertices.length - 1 - 1,
        Nat.sub_lt hLastSegCountPos Nat.zero_lt_one⟩
    have hFirstCutPos : 0 < (cutList eFirst nFirst).length - 1 := by
      have hlen := (endpoint_data eFirst nFirst).1
      exact Nat.sub_pos_of_lt (by omega)
    let kFirst : Fin ((cutList eFirst nFirst).length - 1) :=
      ⟨0, hFirstCutPos⟩
    have hLastCutPos : 0 < (cutList eLast nLast).length - 1 := by
      have hlen := (endpoint_data eLast nLast).1
      exact Nat.sub_pos_of_lt (by omega)
    let kLast : Fin ((cutList eLast nLast).length - 1) :=
      ⟨(cutList eLast nLast).length - 1 - 1,
        Nat.sub_lt hLastCutPos Nat.zero_lt_one⟩
    let sFirst : SegmentIndex := ⟨eFirst, nFirst⟩
    let sLast : SegmentIndex := ⟨eLast, nLast⟩
    let oFirst : OrderIndex := ⟨eFirst, ⟨nFirst, kFirst⟩⟩
    let oLast : OrderIndex := ⟨eLast, ⟨nLast, kLast⟩⟩
    have hEdgeHead :
        (List.finRange E.length).head? = some eFirst := by
      dsimp [eFirst]
      exact finRange_head? E.length hEpos
    have hEdgeLast :
        (List.finRange E.length).getLast? = some eLast := by
      dsimp [eLast]
      exact finRange_getLast? E.length hEpos
    have hSegHead :
        (List.finRange ((E[eFirst.1]'eFirst.2).1.vertices.length - 1)).head? =
          some nFirst := by
      dsimp [nFirst]
      exact finRange_head? ((E[eFirst.1]'eFirst.2).1.vertices.length - 1)
        hFirstSegPos
    have hSegLast :
        (List.finRange ((E[eLast.1]'eLast.2).1.vertices.length - 1)).getLast? =
          some nLast := by
      dsimp [nLast]
      exact finRange_getLast? ((E[eLast.1]'eLast.2).1.vertices.length - 1)
        hLastSegCountPos
    have hCutHead :
        (List.finRange ((cutList eFirst nFirst).length - 1)).head? =
          some kFirst := by
      dsimp [kFirst]
      exact finRange_head? ((cutList eFirst nFirst).length - 1) hFirstCutPos
    have hCutLast :
        (List.finRange ((cutList eLast nLast).length - 1)).getLast? =
          some kLast := by
      dsimp [kLast]
      exact finRange_getLast? ((cutList eLast nLast).length - 1) hLastCutPos
    have hSegmentBlocksHead :
        segmentBlocks.head? = some (edgeSegmentBlock eFirst) := by
      dsimp [segmentBlocks]
      exact map_head?_eq_some edgeSegmentBlock hEdgeHead
    have hSegmentBlocksLast :
        segmentBlocks.getLast? = some (edgeSegmentBlock eLast) := by
      dsimp [segmentBlocks]
      exact map_getLast?_eq_some edgeSegmentBlock hEdgeLast
    have hEdgeSegmentHead :
        (edgeSegmentBlock eFirst).head? = some sFirst := by
      dsimp [edgeSegmentBlock, sFirst]
      exact map_head?_eq_some (fun n => (⟨eFirst, n⟩ : SegmentIndex)) hSegHead
    have hEdgeSegmentLast :
        (edgeSegmentBlock eLast).getLast? = some sLast := by
      dsimp [edgeSegmentBlock, sLast]
      exact map_getLast?_eq_some (fun n => (⟨eLast, n⟩ : SegmentIndex)) hSegLast
    have hSegmentHead : segmentIndexList.head? = some sFirst := by
      rw [segmentIndex_flatten]
      exact flatten_head?_eq_some hSegmentBlocksHead hEdgeSegmentHead
    have hSegmentLast : segmentIndexList.getLast? = some sLast := by
      rw [segmentIndex_flatten]
      exact flatten_getLast?_eq_some hSegmentBlocksLast hEdgeSegmentLast
    have hPieceBlocksHead : pieceBlocks.head? = some (localBlock sFirst) := by
      dsimp [pieceBlocks]
      exact map_head?_eq_some localBlock hSegmentHead
    have hPieceBlocksLast : pieceBlocks.getLast? = some (localBlock sLast) := by
      dsimp [pieceBlocks]
      exact map_getLast?_eq_some localBlock hSegmentLast
    have hLocalHead : (localBlock sFirst).head? = some (pieceAt oFirst) := by
      dsimp [localBlock, sFirst, oFirst]
      exact map_head?_eq_some (fun k => pieceAt ⟨eFirst, ⟨nFirst, k⟩⟩) hCutHead
    have hLocalLast : (localBlock sLast).getLast? = some (pieceAt oLast) := by
      dsimp [localBlock, sLast, oLast]
      exact map_getLast?_eq_some (fun k => pieceAt ⟨eLast, ⟨nLast, k⟩⟩) hCutLast
    have hStreamHead : pieceStream.head? = some (pieceAt oFirst) := by
      rw [pieceStream_flatten]
      exact flatten_head?_eq_some hPieceBlocksHead hLocalHead
    have hStreamLast : pieceStream.getLast? = some (pieceAt oLast) := by
      rw [pieceStream_flatten]
      exact flatten_getLast?_eq_some hPieceBlocksLast hLocalLast
    have hi_eq : i = pieceAt oLast := by
      rw [hStreamLast] at hi
      simpa using hi.symm
    have hj_eq : j = pieceAt oFirst := by
      rw [hStreamHead] at hj
      simpa using hj.symm
    subst i
    subst j
    have hwrapEdge :
        E[eFirst.1]'eFirst.2 = J.successor (E[eLast.1]'eLast.2) := by
      dsimp [eFirst, eLast]
      exact (hEwrap hLastEdge hEpos).symm
    have hnLastVal : nLast.1 + 2 = (E[eLast.1]'eLast.2).1.vertices.length := by
      dsimp [nLast]
      have hlen := (E[eLast.1]'eLast.2).1.length_ge_two
      omega
    have hnFirstVal : nFirst.1 = 0 := by
      rfl
    have hkLastVal : kLast.1 + 1 = (cutList eLast nLast).length - 1 := by
      dsimp [kLast]
      have hlen := (endpoint_data eLast nLast).1
      omega
    have hkFirstVal : kFirst.1 = 0 := by
      rfl
    exact local_next_edge eLast eFirst nLast nFirst kLast kFirst
      hwrapEdge hnLastVal hnFirstVal hkLastVal hkFirstVal
