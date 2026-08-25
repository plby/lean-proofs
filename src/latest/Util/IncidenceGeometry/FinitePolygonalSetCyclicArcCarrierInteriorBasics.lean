import Util.IncidenceGeometry.FinitePolygonalSetCyclicTraversalCuts
import Mathlib.Tactic

open Classical
noncomputable section

lemma FinitePolygonalSetCyclicArcCarrierInteriorBasics
    (J : SimpleClosedPolygonalCurve) (K : FinitePolygonalSet)
    {PieceIndex : Type}
    (successor : Equiv.Perm {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points})
    (pieceArc : PieceIndex → {γ : PolygonalArc // γ ∈ J.edgeArcs})
    (pieceSegmentIndex :
      (i : PieceIndex) → {n : ℕ // n + 1 < (pieceArc i).1.vertices.length})
    (pieceSource pieceTarget : PieceIndex → EuclideanSpace ℝ (Fin 2))
    (pieceSourceParam pieceTargetParam : PieceIndex → Set.Icc (0 : ℝ) 1)
    (pieceSource_eq :
      ∀ i,
        pieceSource i =
          AffineMap.lineMap
            ((pieceArc i).1.vertices[(pieceSegmentIndex i).1]'
              (Nat.lt_of_succ_lt (pieceSegmentIndex i).2))
            ((pieceArc i).1.vertices[(pieceSegmentIndex i).1 + 1]'
              (pieceSegmentIndex i).2)
            (pieceSourceParam i).1)
    (pieceTarget_eq :
      ∀ i,
        pieceTarget i =
          AffineMap.lineMap
            ((pieceArc i).1.vertices[(pieceSegmentIndex i).1]'
              (Nat.lt_of_succ_lt (pieceSegmentIndex i).2))
            ((pieceArc i).1.vertices[(pieceSegmentIndex i).1 + 1]'
              (pieceSegmentIndex i).2)
            (pieceTargetParam i).1)
    (pieceCarrier : PieceIndex → Set (EuclideanSpace ℝ (Fin 2)))
    (pieceCarrier_eq :
      ∀ i, pieceCarrier i = segment ℝ (pieceSource i) (pieceTarget i))
    (arcPieceOrder :
      {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points} → List PieceIndex)
    (arcPieceOrder_nonempty :
      ∀ p : {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points},
        (arcPieceOrder p).length ≠ 0)
    (arcPieceOrder_head_source :
      ∀ (p : {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points}) i,
        (arcPieceOrder p).head? = some i → pieceSource i = p.1)
    (arcPieceOrder_last_target :
      ∀ (p : {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points}) i,
        (arcPieceOrder p).getLast? = some i → pieceTarget i = (successor p).1)
    (arcPieceOrder_consecutive_endpoint :
      ∀ (p : {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points})
        n (hn : n + 1 < (arcPieceOrder p).length),
        pieceTarget ((arcPieceOrder p)[n]) =
          pieceSource ((arcPieceOrder p)[n + 1]))
    (arcPieceOrder_tail_no_source :
      ∀ (p : {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points}) i,
        i ∈ (arcPieceOrder p).tail → pieceSource i ∉ K.points)
    (pieceSource_listed_eq_start :
      ∀ (p : {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points}) i,
        i ∈ arcPieceOrder p → pieceSource i ∈ K.points → pieceSource i = p.1)
    (pieceTarget_listed_eq_target :
      ∀ (p : {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points}) i,
        i ∈ arcPieceOrder p → pieceTarget i ∈ K.points →
          pieceTarget i = (successor p).1)
    (pieceCarrier_covers_curve :
      J.carrier ⊆ ⋃ i : PieceIndex, pieceCarrier i)
    (piece_mem_arcPieceOrder :
      ∀ i : PieceIndex,
        ∃ p : {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points},
          i ∈ arcPieceOrder p)
    (no_listed_open_piece :
      ∀ i (v : EuclideanSpace ℝ (Fin 2)),
        v ∈ K.points → v ∉ openSegment ℝ (pieceSource i) (pieceTarget i)) :
    ∃ (arcCarrier arcInterior :
        {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points} →
          Set (EuclideanSpace ℝ (Fin 2))),
      (∀ p : {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points},
        arcCarrier p =
          ⋃ i : {i : PieceIndex // i ∈ arcPieceOrder p}, pieceCarrier i.1) ∧
      (∀ (p : {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points})
          (i : PieceIndex), i ∈ arcPieceOrder p →
        openSegment ℝ (pieceSource i) (pieceTarget i) ⊆ arcInterior p) ∧
      (∀ (p : {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points})
          n (hn : n + 1 < (arcPieceOrder p).length),
        pieceTarget ((arcPieceOrder p)[n]) ∈ arcInterior p) ∧
      (∀ p : {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points},
        p.1 ∈ arcCarrier p) ∧
      (∀ p : {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points},
        (successor p).1 ∈ arcCarrier p) ∧
      (∀ p : {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points},
        arcCarrier p ⊆ J.carrier) ∧
      (J.carrier ⊆
        ⋃ p : {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points}, arcCarrier p) ∧
      (∀ p : {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points},
        arcInterior p =
          arcCarrier p \ ({p.1, (successor p).1} :
            Set (EuclideanSpace ℝ (Fin 2)))) ∧
      ∀ (p : {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points})
        (v : EuclideanSpace ℝ (Fin 2)),
          v ∈ K.points → v ∉ arcInterior p := by
  classical
  let arcCarrier :
      {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points} →
        Set (EuclideanSpace ℝ (Fin 2)) := fun p =>
    ⋃ i : {i : PieceIndex // i ∈ arcPieceOrder p}, pieceCarrier i.1
  let arcInterior :
      {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points} →
        Set (EuclideanSpace ℝ (Fin 2)) := fun p =>
    arcCarrier p \ ({p.1, (successor p).1} :
      Set (EuclideanSpace ℝ (Fin 2)))
  have hpiece_subset_parent :
      ∀ q : PieceIndex,
        pieceCarrier q ⊆
          segment ℝ
            ((pieceArc q).1.vertices[(pieceSegmentIndex q).1]'
              (Nat.lt_of_succ_lt (pieceSegmentIndex q).2))
            ((pieceArc q).1.vertices[(pieceSegmentIndex q).1 + 1]'
              (pieceSegmentIndex q).2) := by
    intro q x hx
    rw [pieceCarrier_eq q] at hx
    have hs :
        pieceSource q ∈
          segment ℝ
            ((pieceArc q).1.vertices[(pieceSegmentIndex q).1]'
              (Nat.lt_of_succ_lt (pieceSegmentIndex q).2))
            ((pieceArc q).1.vertices[(pieceSegmentIndex q).1 + 1]'
              (pieceSegmentIndex q).2) := by
      rw [pieceSource_eq q, segment_eq_image_lineMap]
      exact ⟨(pieceSourceParam q).1, (pieceSourceParam q).2, rfl⟩
    have ht :
        pieceTarget q ∈
          segment ℝ
            ((pieceArc q).1.vertices[(pieceSegmentIndex q).1]'
              (Nat.lt_of_succ_lt (pieceSegmentIndex q).2))
            ((pieceArc q).1.vertices[(pieceSegmentIndex q).1 + 1]'
              (pieceSegmentIndex q).2) := by
      rw [pieceTarget_eq q, segment_eq_image_lineMap]
      exact ⟨(pieceTargetParam q).1, (pieceTargetParam q).2, rfl⟩
    exact (convex_segment _ _).segment_subset hs ht hx
  have hpiece_subset_arc :
      ∀ q : PieceIndex, pieceCarrier q ⊆ (pieceArc q).1.carrier := by
    intro q x hx
    rw [(pieceArc q).1.carrier_eq]
    exact ⟨(pieceSegmentIndex q).1, (pieceSegmentIndex q).2,
      hpiece_subset_parent q hx⟩
  refine ⟨arcCarrier, arcInterior, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p
    rfl
  · intro p i hi x hx
    refine ⟨?_, ?_⟩
    · exact Set.mem_iUnion.2
        ⟨⟨i, hi⟩, by
          rw [pieceCarrier_eq i]
          exact openSegment_subset_segment ℝ (pieceSource i) (pieceTarget i) hx⟩
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      constructor
      · intro hxstart
        exact no_listed_open_piece i p.1 p.2 (by simpa [hxstart] using hx)
      · intro hxend
        exact no_listed_open_piece i (successor p).1 (successor p).2
          (by simpa [hxend] using hx)
  · intro p n hn
    let i : PieceIndex := (arcPieceOrder p)[n]
    let j : PieceIndex := (arcPieceOrder p)[n + 1]
    have hi_mem : i ∈ arcPieceOrder p := by
      exact List.getElem_mem (l := arcPieceOrder p) (n := n) (by omega)
    have hj_tail : j ∈ (arcPieceOrder p).tail := by
      have hn_tail : n < (arcPieceOrder p).tail.length := by
        rw [List.length_tail]
        omega
      have hget : (arcPieceOrder p).tail[n] = (arcPieceOrder p)[n + 1] :=
        List.getElem_tail hn_tail
      simpa [j, hget] using
        List.getElem_mem (l := (arcPieceOrder p).tail) (n := n) hn_tail
    have hjoin : pieceTarget i = pieceSource j := by
      simpa [i, j] using arcPieceOrder_consecutive_endpoint p n hn
    refine ⟨?_, ?_⟩
    · exact Set.mem_iUnion.2
        ⟨⟨i, hi_mem⟩, by
          rw [pieceCarrier_eq i]
          exact right_mem_segment ℝ (pieceSource i) (pieceTarget i)⟩
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      constructor
      · intro hstart
        have hsrcj : pieceSource j = p.1 := hjoin.symm.trans hstart
        exact (arcPieceOrder_tail_no_source p j hj_tail) (by simpa [hsrcj] using p.2)
      · intro hend
        have hsrcj : pieceSource j = (successor p).1 := hjoin.symm.trans hend
        exact (arcPieceOrder_tail_no_source p j hj_tail)
          (by simpa [hsrcj] using (successor p).2)
  · intro p
    let L := arcPieceOrder p
    have hLne : L ≠ [] := by
      intro hnil
      have hlen : (arcPieceOrder p).length = 0 := by simpa [L, hnil]
      exact arcPieceOrder_nonempty p hlen
    let i : PieceIndex := L.head hLne
    have hi_mem : i ∈ arcPieceOrder p := by
      simpa [L, i] using List.head_mem hLne
    have hhead : (arcPieceOrder p).head? = some i := by
      simpa [L, i] using List.head?_eq_some_head hLne
    have hsource : pieceSource i = p.1 := arcPieceOrder_head_source p i hhead
    exact Set.mem_iUnion.2
      ⟨⟨i, hi_mem⟩, by
        rw [pieceCarrier_eq i]
        simpa [hsource] using left_mem_segment ℝ (pieceSource i) (pieceTarget i)⟩
  · intro p
    let L := arcPieceOrder p
    have hLne : L ≠ [] := by
      intro hnil
      have hlen : (arcPieceOrder p).length = 0 := by simpa [L, hnil]
      exact arcPieceOrder_nonempty p hlen
    let i : PieceIndex := L.getLast hLne
    have hi_mem : i ∈ arcPieceOrder p := by
      simpa [L, i] using List.getLast_mem hLne
    have hlast : (arcPieceOrder p).getLast? = some i := by
      simpa [L, i] using List.getLast?_eq_some_getLast hLne
    have htarget : pieceTarget i = (successor p).1 :=
      arcPieceOrder_last_target p i hlast
    exact Set.mem_iUnion.2
      ⟨⟨i, hi_mem⟩, by
        rw [pieceCarrier_eq i]
        simpa [htarget] using right_mem_segment ℝ (pieceSource i) (pieceTarget i)⟩
  · intro p x hx
    rcases Set.mem_iUnion.mp hx with ⟨i, hxi⟩
    rw [J.carrier_eq]
    exact Set.mem_iUnion.2 ⟨pieceArc i.1, hpiece_subset_arc i.1 hxi⟩
  · intro x hxJ
    rcases Set.mem_iUnion.mp (pieceCarrier_covers_curve hxJ) with ⟨i, hxi⟩
    rcases piece_mem_arcPieceOrder i with ⟨p, hi⟩
    exact Set.mem_iUnion.2
      ⟨p, Set.mem_iUnion.2 ⟨⟨i, hi⟩, hxi⟩⟩
  · intro p
    rfl
  · intro p v hvK hvInterior
    rcases hvInterior with ⟨hvCarrier, hvNotEndpoint⟩
    rcases Set.mem_iUnion.mp hvCarrier with ⟨i, hvi⟩
    have hseg : v ∈ segment ℝ (pieceSource i.1) (pieceTarget i.1) := by
      simpa [pieceCarrier_eq i.1] using hvi
    have hdecomp :
        v ∈ insert (pieceSource i.1)
          (insert (pieceTarget i.1)
            (openSegment ℝ (pieceSource i.1) (pieceTarget i.1))) := by
      simpa [insert_endpoints_openSegment ℝ (pieceSource i.1) (pieceTarget i.1)]
        using hseg
    simp only [Set.mem_insert_iff] at hdecomp
    rcases hdecomp with hvsource | hvtarget | hvopen
    · have hsourceK : pieceSource i.1 ∈ K.points := by
        simpa [hvsource] using hvK
      have hsource : pieceSource i.1 = p.1 :=
        pieceSource_listed_eq_start p i.1 i.2 hsourceK
      exact hvNotEndpoint (by simp [hvsource, hsource])
    · have htargetK : pieceTarget i.1 ∈ K.points := by
        simpa [hvtarget] using hvK
      have htarget : pieceTarget i.1 = (successor p).1 :=
        pieceTarget_listed_eq_target p i.1 i.2 htargetK
      exact hvNotEndpoint (by simp [hvtarget, htarget])
    · exact no_listed_open_piece i.1 v hvK hvopen
