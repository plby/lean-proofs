import ErdosProblems.Erdos733.ST.FinitePolygonalSet

open Classical
noncomputable section

-- [TABLET NODE: FinitePolygonalSetCyclicSourceOccurrenceCollapse]
lemma FinitePolygonalSetCyclicSourceOccurrenceCollapse
    (K : FinitePolygonalSet)
    {PieceIndex : Type}
    (pieceStream : List PieceIndex)
    (pieceSource pieceTarget : PieceIndex → EuclideanSpace ℝ (Fin 2))
    (hstream_pos : 0 < pieceStream.length)
    (hadjacent :
      ∀ n (hn : n + 1 < pieceStream.length),
        pieceTarget pieceStream[n] = pieceSource pieceStream[n + 1])
    (hcyclic :
      ∀ i, pieceStream.getLast? = some i →
        ∀ j, pieceStream.head? = some j → pieceTarget i = pieceSource j)
    (rawOccurrenceList : List (EuclideanSpace ℝ (Fin 2)))
    (hraw_eq :
      rawOccurrenceList =
        List.flatMap (fun i =>
          (if pieceSource i ∈ K.points then [pieceSource i] else []) ++
          (if pieceTarget i ∈ K.points then [pieceTarget i] else []))
          pieceStream)
    (hraw_covers :
      ∀ p : {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points},
        p.1 ∈ rawOccurrenceList) :
    ∃ sourceOccurrenceList :
        List {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points},
      sourceOccurrenceList =
        List.flatMap (fun i =>
          if h : pieceSource i ∈ K.points then [⟨pieceSource i, h⟩] else [])
          pieceStream ∧
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
-- BODY
  classical
  let sourceOccurrenceList :
      List {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points} :=
    List.flatMap (fun i =>
      if h : pieceSource i ∈ K.points then [⟨pieceSource i, h⟩] else [])
      pieceStream
  have hhead0 : pieceStream.head? = some pieceStream[0] := by
    rw [List.head?_eq_getElem?]
    rw [List.getElem?_eq_getElem hstream_pos]
  have raw_mem_source :
      ∀ {x : EuclideanSpace ℝ (Fin 2)} (hxK : x ∈ K.points),
        x ∈ List.flatMap (fun i =>
          (if pieceSource i ∈ K.points then [pieceSource i] else []) ++
          (if pieceTarget i ∈ K.points then [pieceTarget i] else []))
          pieceStream →
        (⟨x, hxK⟩ : {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points}) ∈
          sourceOccurrenceList := by
    intro x hxK hx
    rw [List.mem_flatMap] at hx
    rcases hx with ⟨i, hi, hxinner⟩
    rw [List.mem_append] at hxinner
    rcases hxinner with hxsource | hxtarget
    · by_cases hs : pieceSource i ∈ K.points
      · simp [hs] at hxsource
        subst x
        dsimp [sourceOccurrenceList]
        rw [List.mem_flatMap]
        refine ⟨i, hi, ?_⟩
        simp [hs]
      · simp [hs] at hxsource
    · by_cases ht : pieceTarget i ∈ K.points
      · simp [ht] at hxtarget
        subst x
        rcases List.getElem_of_mem hi with ⟨n, hn, hi_eq⟩
        subst i
        by_cases hnext : n + 1 < pieceStream.length
        · have hjoin := hadjacent n hnext
          have hsnext : pieceSource pieceStream[n + 1] ∈ K.points := by
            simpa [← hjoin] using hxK
          dsimp [sourceOccurrenceList]
          rw [List.mem_flatMap]
          refine ⟨pieceStream[n + 1],
            List.getElem_mem (l := pieceStream) (n := n + 1) hnext, ?_⟩
          simpa [hsnext] using hjoin
        · have hnlast : n = pieceStream.length - 1 := by omega
          have hlast : pieceStream.getLast? = some pieceStream[n] := by
            rw [List.getLast?_eq_getElem?]
            have hidx : pieceStream.length - 1 = n := by omega
            simp [hidx]
          have hjoin := hcyclic (pieceStream[n]) hlast (pieceStream[0]) hhead0
          have hsfirst : pieceSource pieceStream[0] ∈ K.points := by
            simpa [← hjoin] using hxK
          dsimp [sourceOccurrenceList]
          rw [List.mem_flatMap]
          refine ⟨pieceStream[0],
            List.getElem_mem (l := pieceStream) (n := 0) hstream_pos, ?_⟩
          simpa [hsfirst] using hjoin
      · simp [ht] at hxtarget
  refine ⟨sourceOccurrenceList, rfl, ?_, ?_, ?_, ?_⟩
  · intro q _hq
    exact q.2
  · intro p
    apply raw_mem_source p.2
    simpa [hraw_eq] using hraw_covers p
  · intro q hq
    dsimp [sourceOccurrenceList] at hq
    rw [List.mem_flatMap] at hq
    rcases hq with ⟨i, hi, hqi⟩
    by_cases hs : pieceSource i ∈ K.points
    · simp [hs] at hqi
      subst q
      exact ⟨i, hi, rfl⟩
    · simp [hs] at hqi
  · intro q hq
    dsimp [sourceOccurrenceList] at hq
    rw [List.mem_flatMap] at hq
    rcases hq with ⟨i, hi, hqi⟩
    by_cases hs : pieceSource i ∈ K.points
    · simp [hs] at hqi
      subst q
      rcases List.getElem_of_mem hi with ⟨n, hn, hi_eq⟩
      subst i
      refine ⟨n, hn, rfl, ?_⟩
      by_cases hn0 : n = 0
      · left
        refine ⟨hn0, ?_⟩
        intro last hlast
        have hjoin := hcyclic last hlast (pieceStream[0]) hhead0
        simpa [hn0] using hjoin
      · right
        have hnpos : 0 < n := by omega
        refine ⟨hnpos, ?_⟩
        have hprev : n - 1 + 1 < pieceStream.length := by omega
        have hjoin := hadjacent (n - 1) hprev
        have hidx : n - 1 + 1 = n := by omega
        simpa [hidx] using hjoin
    · simp [hs] at hqi
