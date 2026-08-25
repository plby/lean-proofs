import Util.IncidenceGeometry.FinitePolygonalSetCyclicFilteredStreamIntervals
import Util.IncidenceGeometry.FinitePolygonalSetCyclicNormalizedSourceSuccessorOrder
import Util.IncidenceGeometry.FinitePolygonalSetCarrierEqSimpleClosedCurvePointsTwo
import Mathlib.Tactic

open Classical
noncomputable section

lemma FinitePolygonalSetCyclicActualStreamIntervalBlocks
    (J : SimpleClosedPolygonalCurve) (K : FinitePolygonalSet)
    (hKJ : K.carrier = J.carrier)
    {PieceIndex : Type}
    (pieceStream : List PieceIndex)
    (pieceSource pieceTarget :
      PieceIndex → EuclideanSpace ℝ (Fin 2))
    (ConsecutiveOK : PieceIndex → PieceIndex → Prop)
    (consecutive_endpoint :
      ∀ i j : PieceIndex, ConsecutiveOK i j →
        pieceTarget i = pieceSource j)
    (stream_consecutive :
      ∀ n (hn : n + 1 < pieceStream.length),
        ConsecutiveOK pieceStream[n] pieceStream[n + 1])
    (stream_cyclic :
      ∀ i, pieceStream.getLast? = some i →
        ∀ j, pieceStream.head? = some j → ConsecutiveOK i j)
    (sourceOccurrenceList :
      List {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points})
    (hsource_eq :
      sourceOccurrenceList =
        List.flatMap (fun i =>
          if h : pieceSource i ∈ K.points then
            [(⟨pieceSource i, h⟩ :
              {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points})]
          else [])
          pieceStream)
    (hsource_nodup : sourceOccurrenceList.Nodup)
    (hsource_covers :
      ∀ p : {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points},
        p ∈ sourceOccurrenceList) :
    ∃ successor : Equiv.Perm {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points},
      successor = sourceOccurrenceList.formPerm ∧
        (∀ p q : {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points},
          ∃ n : ℕ, (successor^[n]) p = q) ∧
        (∀ p : {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points},
          p.1 ≠ (successor p).1) ∧
        ∀ p : {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points},
          ∃ arcPieceOrder : List PieceIndex,
            arcPieceOrder.length ≠ 0 ∧
              (∀ i, arcPieceOrder.head? = some i → pieceSource i = p.1) ∧
                (∀ i, arcPieceOrder.getLast? = some i →
                  pieceTarget i = (successor p).1) ∧
                  List.IsChain ConsecutiveOK arcPieceOrder ∧
                    (∀ i, i ∈ arcPieceOrder.tail →
                      pieceSource i ∉ K.points) ∧
                      (∀ i, i ∈ arcPieceOrder → i ∈ pieceStream) ∧
                        ((∃ (pre : List PieceIndex) (head : PieceIndex)
                              (middle : List PieceIndex) (next : PieceIndex)
                              (suffix : List PieceIndex),
                            arcPieceOrder = head :: middle ∧
                              pieceStream =
                                pre ++ arcPieceOrder ++ (next :: suffix) ∧
                              pieceSource head = p.1 ∧
                              pieceSource next = (successor p).1 ∧
                              ∀ i ∈ middle, pieceSource i ∉ K.points) ∨
                          (∃ (pre : List PieceIndex) (next : PieceIndex)
                              (middle : List PieceIndex) (head : PieceIndex)
                              (suffix : List PieceIndex),
                            arcPieceOrder = head :: (suffix ++ pre) ∧
                              pieceStream =
                                pre ++ (next :: middle) ++ (head :: suffix) ∧
                              pieceSource head = p.1 ∧
                              pieceSource next = (successor p).1 ∧
                              ∀ i ∈ suffix ++ pre,
                                pieceSource i ∉ K.points)) := by
  classical
  let α := {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points}
  let sourceOption : PieceIndex → Option α := fun i =>
    if h : pieceSource i ∈ K.points then some ⟨pieceSource i, h⟩ else none
  have hsource_filter :
      sourceOccurrenceList = pieceStream.filterMap sourceOption := by
    rw [hsource_eq, List.filterMap_eq_flatMap_toList]
    congr 1
    funext i
    by_cases h : pieceSource i ∈ K.points
    · simp [sourceOption, h]
    · simp [sourceOption, h]
  have hlen_two : 2 ≤ sourceOccurrenceList.length := by
    have hpoints_two : 1 < K.points.card := by
      have htwo := FinitePolygonalSetCarrierEqSimpleClosedCurvePointsTwo J K hKJ
      omega
    rcases Finset.one_lt_card.1 hpoints_two with ⟨a, ha, b, hb, hab⟩
    let pa : α := ⟨a, ha⟩
    let pb : α := ⟨b, hb⟩
    have hpane : pa ≠ pb := by
      intro h
      exact hab (congrArg Subtype.val h)
    have hpair_subset :
        ({pa, pb} : Finset α) ⊆ sourceOccurrenceList.toFinset := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · simpa using hsource_covers pa
      · simpa using hsource_covers pb
    have hpair_card : ({pa, pb} : Finset α).card = 2 := by
      simp [hpane]
    have hcard_le := Finset.card_le_card hpair_subset
    have htoFinset_card :
        sourceOccurrenceList.toFinset.card = sourceOccurrenceList.length :=
      List.toFinset_card_of_nodup hsource_nodup
    omega
  rcases
    FinitePolygonalSetCyclicNormalizedSourceSuccessorOrder
      J K hKJ sourceOccurrenceList hsource_nodup hsource_covers with
    ⟨successor, hsuccessor_eq, hsuccessor_cycle, hsuccessor_nondeg⟩
  have sourceOption_some :
      ∀ (i : PieceIndex) (q : α), sourceOption i = some q →
        pieceSource i = q.1 := by
    intro i q hsome
    dsimp [sourceOption] at hsome
    by_cases h : pieceSource i ∈ K.points
    · simp [h] at hsome
      exact congrArg Subtype.val hsome
    · simp [h] at hsome
  have sourceOption_none :
      ∀ i : PieceIndex, sourceOption i = none →
        pieceSource i ∉ K.points := by
    intro i hnone hmem
    dsimp [sourceOption] at hnone
    simp [hmem] at hnone
  have stream_chain : List.IsChain ConsecutiveOK pieceStream := by
    rw [List.isChain_iff_getElem]
    intro i hi
    exact stream_consecutive i hi
  refine ⟨successor, hsuccessor_eq, hsuccessor_cycle,
    hsuccessor_nondeg, ?_⟩
  intro p
  have hp_mem : p ∈ sourceOccurrenceList := hsource_covers p
  rcases
    FinitePolygonalSetCyclicFilteredStreamIntervals
      pieceStream sourceOption sourceOccurrenceList hsource_filter
      hsource_nodup hlen_two p hp_mem with
    ⟨_hp_ne, hcases⟩
  rcases hcases with hnonwrap | hwrap
  · rcases hnonwrap with
      ⟨pre, head, middle, next, suffix, hstream, hhead, hnext, hnone⟩
    let block : List PieceIndex := head :: middle
    have hhead_source : pieceSource head = p.1 :=
      sourceOption_some head p hhead
    have hnext_source :
        pieceSource next = (successor p).1 := by
      have hsrc := sourceOption_some next (sourceOccurrenceList.formPerm p) hnext
      simpa [hsuccessor_eq] using hsrc
    have chain_decomp :
        List.IsChain ConsecutiveOK
          (pre ++ block ++ (next :: suffix)) := by
      simpa [block, hstream] using stream_chain
    have chain_decomp' :
        List.IsChain ConsecutiveOK
          (pre ++ (block ++ (next :: suffix))) := by
      simpa [List.append_assoc] using chain_decomp
    have chain_block_next_suffix :
        List.IsChain ConsecutiveOK (block ++ (next :: suffix)) :=
      (List.isChain_append.mp chain_decomp').2.1
    have block_chain : List.IsChain ConsecutiveOK block :=
      (List.isChain_append.mp chain_block_next_suffix).1
    have cross_block_next :
        ∀ x ∈ block.getLast?, ∀ y ∈ (next :: suffix).head?,
          ConsecutiveOK x y :=
      (List.isChain_append.mp chain_block_next_suffix).2.2
    have hlast_target :
        ∀ i, block.getLast? = some i →
          pieceTarget i = (successor p).1 := by
      intro i hi
      have hR : ConsecutiveOK i next := by
        exact cross_block_next i (by simp [hi]) next (by simp)
      exact (consecutive_endpoint i next hR).trans hnext_source
    have htail_no_source :
        ∀ i, i ∈ block.tail → pieceSource i ∉ K.points := by
      intro i hi
      have him : i ∈ middle := by
        simpa [block] using hi
      exact sourceOption_none i (hnone i him)
    have hmem_stream : ∀ i, i ∈ block → i ∈ pieceStream := by
      intro i hi
      rw [hstream]
      simp [block] at hi ⊢
      tauto
    refine ⟨block, by simp [block], ?_, hlast_target, block_chain,
      htail_no_source, hmem_stream, Or.inl ?_⟩
    · intro i hi
      have : head = i := by simpa [block] using hi
      subst i
      exact hhead_source
    · refine ⟨pre, head, middle, next, suffix, rfl, ?_, hhead_source,
        hnext_source, ?_⟩
      · simpa [block] using hstream
      · intro i hi
        exact sourceOption_none i (hnone i hi)
  · rcases hwrap with
      ⟨pre, next, middle, head, suffix, hstream, hhead, hnext, hnone⟩
    let block : List PieceIndex := head :: (suffix ++ pre)
    have hhead_source : pieceSource head = p.1 :=
      sourceOption_some head p hhead
    have hnext_source :
        pieceSource next = (successor p).1 := by
      have hsrc := sourceOption_some next (sourceOccurrenceList.formPerm p) hnext
      simpa [hsuccessor_eq] using hsrc
    have chain_decomp :
        List.IsChain ConsecutiveOK
          (pre ++ (next :: middle) ++ (head :: suffix)) := by
      simpa [hstream] using stream_chain
    have chain_pre_next :
        List.IsChain ConsecutiveOK (pre ++ (next :: middle)) :=
      (List.isChain_append.mp chain_decomp).1
    have chain_pre : List.IsChain ConsecutiveOK pre :=
      (List.isChain_append.mp chain_pre_next).1
    have chain_head_suffix : List.IsChain ConsecutiveOK (head :: suffix) :=
      (List.isChain_append.mp chain_decomp).2.1
    have cross_pre_next :
        ∀ x ∈ pre.getLast?, ∀ y ∈ (next :: middle).head?,
          ConsecutiveOK x y :=
      (List.isChain_append.mp chain_pre_next).2.2
    have cross_cyclic :
        ∀ x ∈ (head :: suffix).getLast?, ∀ y ∈ pre.head?,
          ConsecutiveOK x y := by
      intro x hx y hy
      have hxsome : (head :: suffix).getLast? = some x := by
        simpa using hx
      have hysome : pre.head? = some y := by
        simpa using hy
      have hxstream : pieceStream.getLast? = some x := by
        rw [hstream, List.getLast?_append, hxsome, Option.some_or]
      have hystream : pieceStream.head? = some y := by
        rw [hstream]
        cases pre with
        | nil =>
            simp at hysome
        | cons a as =>
            simpa using hysome
      exact stream_cyclic x hxstream y hystream
    have block_chain : List.IsChain ConsecutiveOK block := by
      have hchain :=
        List.IsChain.append chain_head_suffix chain_pre cross_cyclic
      simpa [block, List.cons_append] using hchain
    have hlast_target :
        ∀ i, block.getLast? = some i →
          pieceTarget i = (successor p).1 := by
      intro i hi
      cases pre with
      | nil =>
          have hi_tail : (head :: suffix).getLast? = some i := by
            simpa [block] using hi
          have hxstream : pieceStream.getLast? = some i := by
            rw [hstream]
            change ((next :: middle) ++ (head :: suffix)).getLast? = some i
            rw [List.getLast?_append, hi_tail, Option.some_or]
          have hnext_head : pieceStream.head? = some next := by
            rw [hstream]
            simp
          have hR : ConsecutiveOK i next :=
            stream_cyclic i hxstream next hnext_head
          exact (consecutive_endpoint i next hR).trans hnext_source
      | cons a as =>
          have hi_pre : (a :: as).getLast? = some i := by
            have hblock_eq : block = (head :: suffix) ++ (a :: as) := by
              simp [block, List.cons_append]
            rw [hblock_eq, List.getLast?_append] at hi
            simpa using hi
          have hR : ConsecutiveOK i next := by
            exact cross_pre_next i (by simp [hi_pre]) next (by simp)
          exact (consecutive_endpoint i next hR).trans hnext_source
    have htail_no_source :
        ∀ i, i ∈ block.tail → pieceSource i ∉ K.points := by
      intro i hi
      have him : i ∈ suffix ++ pre := by
        simpa [block] using hi
      exact sourceOption_none i (hnone i him)
    have hmem_stream : ∀ i, i ∈ block → i ∈ pieceStream := by
      intro i hi
      rw [hstream]
      simp [block] at hi ⊢
      tauto
    refine ⟨block, by simp [block], ?_, hlast_target, block_chain,
      htail_no_source, hmem_stream, Or.inr ?_⟩
    · intro i hi
      have : head = i := by simpa [block] using hi
      subst i
      exact hhead_source
    · refine ⟨pre, next, middle, head, suffix, rfl, hstream,
        hhead_source, hnext_source, ?_⟩
      intro i hi
      exact sourceOption_none i (hnone i hi)

