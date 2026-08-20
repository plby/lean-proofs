import ErdosProblems.Erdos733.ST.FinitePolygonalSetCyclicOrderedPieceContainedInListedSegment
import ErdosProblems.Erdos733.ST.FinitePolygonalSetCyclicAdjacentPiecesSameListedSegment

open Classical
noncomputable section

-- [TABLET NODE: FinitePolygonalSetCyclicArcCarrierContainedInListedSegment]
lemma FinitePolygonalSetCyclicArcCarrierContainedInListedSegment
    (J : SimpleClosedPolygonalCurve) (K : FinitePolygonalSet)
    (hKJ : K.carrier = J.carrier)
    (D : FinitePolygonalSetCyclicTraversalCuts J K)
    (p : {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points}) :
    ∃ s : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2),
      s ∈ K.segments ∧ D.arcCarrier p ⊆ segment ℝ s.1 s.2 := by
-- BODY
  let L : List D.pieceIndex := D.arcPieceOrder p
  have hlen_pos : 0 < L.length := Nat.pos_of_ne_zero (D.arcPieceOrder_nonempty p)
  let i0 : D.pieceIndex := L[0]'hlen_pos
  have hi0 : i0 ∈ D.arcPieceOrder p := by
    simpa [L, i0] using List.getElem_mem (l := L) hlen_pos
  rcases
    FinitePolygonalSetCyclicOrderedPieceContainedInListedSegment
      J K hKJ D p i0 hi0 with
    ⟨s, hs, hs0⟩
  have hindex_subset :
      ∀ n (hn : n < L.length),
        D.pieceCarrier (L[n]'hn) ⊆ segment ℝ s.1 s.2 := by
    intro n hn
    induction n with
    | zero =>
        simpa [L, i0] using hs0
    | succ n ih =>
        have hn_prev : n < L.length := Nat.lt_trans (Nat.lt_succ_self n) hn
        have hprev : D.pieceCarrier (L[n]'hn_prev) ⊆ segment ℝ s.1 s.2 :=
          ih hn_prev
        have hmem_next : L[n + 1]'hn ∈ D.arcPieceOrder p := by
          simpa [L] using List.getElem_mem (l := L) hn
        rcases
          FinitePolygonalSetCyclicOrderedPieceContainedInListedSegment
            J K hKJ D p (L[n + 1]'hn) hmem_next with
          ⟨t, ht, htcont⟩
        have hsame : s = t :=
          FinitePolygonalSetCyclicAdjacentPiecesSameListedSegment
            J K D p n (by simpa [L] using hn) s t hs ht
            (by simpa [L] using hprev)
            (by simpa [L] using htcont)
        simpa [hsame] using htcont
  have hall_pieces :
      ∀ i : D.pieceIndex, i ∈ D.arcPieceOrder p →
        D.pieceCarrier i ⊆ segment ℝ s.1 s.2 := by
    intro i hi
    rcases List.getElem_of_mem hi with ⟨n, hn, hget⟩
    simpa [L, hget] using hindex_subset n (by simpa [L] using hn)
  refine ⟨s, hs, ?_⟩
  intro x hx
  rw [D.arcCarrier_eq_pieceOrder p] at hx
  rcases Set.mem_iUnion.mp hx with ⟨i, hxi⟩
  exact hall_pieces i.1 i.2 hxi
