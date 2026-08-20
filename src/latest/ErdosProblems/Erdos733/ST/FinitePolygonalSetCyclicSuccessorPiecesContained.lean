import ErdosProblems.Erdos733.ST.FinitePolygonalSetCyclicSuccessorOrder
import ErdosProblems.Erdos733.ST.FinitePolygonalSetCyclicOrderedPieceCoveredByListedSegments
import ErdosProblems.Erdos733.ST.FinitePolygonalSetCyclicOrderedPieceContainedInListedSegment
import ErdosProblems.Erdos733.ST.FinitePolygonalSetCyclicArcCarrierContainedInListedSegment
import ErdosProblems.Erdos733.ST.FinitePolygonalSetCyclicAdjacentPiecesSameListedSegment
import ErdosProblems.Erdos733.ST.FinitePolygonalSetCyclicAdjacentPieceCarriersMeetAtJunction
import ErdosProblems.Erdos733.ST.FinitePolygonalSetCyclicNonadjacentActualPiecesDisjoint
import ErdosProblems.Erdos733.ST.FinitePolygonalSetCyclicSameArcSeparatedActualPiecesDisjoint
import ErdosProblems.Erdos733.ST.CollinearSegmentChainUnion

open Classical
noncomputable section

-- [TABLET NODE: FinitePolygonalSetCyclicSuccessorPiecesContained]
lemma FinitePolygonalSetCyclicSuccessorPiecesContained
    (J : SimpleClosedPolygonalCurve) (K : FinitePolygonalSet)
    (hKJ : K.carrier = J.carrier)
    (D : FinitePolygonalSetCyclicTraversalCuts J K) :
    (J.carrier =
      ⋃ p : {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points},
        segment ℝ p.1 (D.successor p).1) ∧
      (∀ p : {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points},
        ∃ s : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2),
          s ∈ K.segments ∧
            segment ℝ p.1 (D.successor p).1 ⊆ segment ℝ s.1 s.2) ∧
      (∀ p : {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points},
        D.arcCarrier p = segment ℝ p.1 (D.successor p).1) ∧
      (∀ p : {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points},
        openSegment ℝ p.1 (D.successor p).1 ⊆ D.arcInterior p) ∧
      (∀ (p : {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points})
          (v : EuclideanSpace ℝ (Fin 2)),
        v ∈ K.points → v ∉ openSegment ℝ p.1 (D.successor p).1) ∧
      (∀ p q : {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points},
        p ≠ q →
          Disjoint (openSegment ℝ p.1 (D.successor p).1)
            (openSegment ℝ q.1 (D.successor q).1)) := by
-- BODY
  have hArcCarrier :
      ∀ p : {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points},
        D.arcCarrier p = segment ℝ p.1 (D.successor p).1 := by
    intro p
    rcases
      FinitePolygonalSetCyclicArcCarrierContainedInListedSegment J K hKJ D p with
      ⟨s, hs, hArcSubset⟩
    let Lidx : List D.pieceIndex := D.arcPieceOrder p
    let L : List (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)) :=
      Lidx.map fun i => (D.pieceSource i, D.pieceTarget i)
    have hLidx_pos : 0 < Lidx.length := Nat.pos_of_ne_zero (D.arcPieceOrder_nonempty p)
    have hL_pos : 0 < L.length := by
      simpa [L, Lidx] using hLidx_pos
    have hL_len : L.length = Lidx.length := by
      simp [L]
    have hPiece_mem :
        ∀ n (hn : n < Lidx.length), Lidx[n]'hn ∈ D.arcPieceOrder p := by
      intro n hn
      simpa [Lidx] using List.getElem_mem (l := Lidx) hn
    have hPiece_subset_arc :
        ∀ n (hn : n < Lidx.length),
          D.pieceCarrier (Lidx[n]'hn) ⊆ D.arcCarrier p := by
      intro n hn x hx
      rw [D.arcCarrier_eq_pieceOrder p]
      exact Set.mem_iUnion.2
        ⟨⟨Lidx[n]'hn, hPiece_mem n hn⟩, by simpa using hx⟩
    have hcontained :
        ∀ n (hn : n < L.length),
          segment ℝ (L[n]).1 (L[n]).2 ⊆ segment ℝ s.1 s.2 := by
      intro n hn x hx
      have hnidx : n < Lidx.length := by simpa [hL_len] using hn
      have hxpiece : x ∈ D.pieceCarrier (Lidx[n]'hnidx) := by
        rw [D.pieceCarrier_eq]
        simpa [L, Lidx] using hx
      exact hArcSubset (hPiece_subset_arc n hnidx hxpiece)
    have hlink :
        ∀ n (hn : n + 1 < L.length), (L[n]).2 = (L[n + 1]).1 := by
      intro n hn
      have hnidx : n + 1 < Lidx.length := by simpa [hL_len] using hn
      have hconsec := D.arcPieceOrder_consecutive p n hnidx
      simpa [L, Lidx] using hconsec.1
    have hne :
        ∀ n (hn : n < L.length), (L[n]).1 ≠ (L[n]).2 := by
      intro n hn h_eq
      have hnidx : n < Lidx.length := by simpa [hL_len] using hn
      let i : D.pieceIndex := Lidx[n]'hnidx
      have hverts_ne :
          (D.pieceArc i).1.vertices[(D.pieceSegmentIndex i).1]'
              (Nat.lt_of_succ_lt (D.pieceSegmentIndex i).2) ≠
            (D.pieceArc i).1.vertices[(D.pieceSegmentIndex i).1 + 1]'
              (D.pieceSegmentIndex i).2 := by
        intro hv
        have hidx :
            (D.pieceSegmentIndex i).1 = (D.pieceSegmentIndex i).1 + 1 :=
          ((D.pieceArc i).1.simple_vertices.getElem_inj_iff).mp hv
        omega
      have hsrc_tgt : D.pieceSource i = D.pieceTarget i := by
        simpa [L, Lidx, i] using h_eq
      have hparam_eq :
          (D.pieceSourceParam i).1 = (D.pieceTargetParam i).1 := by
        apply AffineMap.lineMap_injective ℝ hverts_ne
        simpa [D.pieceSource_eq i, D.pieceTarget_eq i] using hsrc_tgt
      have hsub_eq : D.pieceSourceParam i = D.pieceTargetParam i :=
        Subtype.ext hparam_eq
      exact (ne_of_lt (D.pieceSourceParam_lt_targetParam i)) hsub_eq
    have hinter :
        ∀ n (hn : n + 1 < L.length),
          segment ℝ (L[n]).1 (L[n]).2 ∩
              segment ℝ (L[n + 1]).1 (L[n + 1]).2 =
            ({(L[n]).2} : Set (EuclideanSpace ℝ (Fin 2))) := by
      intro n hn
      have hnidx : n + 1 < Lidx.length := by simpa [hL_len] using hn
      have hmeet :=
        FinitePolygonalSetCyclicAdjacentPieceCarriersMeetAtJunction J K D p n hnidx
      simpa [L, Lidx, D.pieceCarrier_eq] using hmeet
    have hstraight :=
      CollinearSegmentChainUnion s.1 s.2 (K.segment_nondegenerate s hs)
        L hL_pos hcontained hlink hne hinter
    have hArc_as_L :
        D.arcCarrier p =
          ⋃ k : Fin L.length, segment ℝ (L[k.1]).1 (L[k.1]).2 := by
      apply Set.ext
      intro x
      constructor
      · intro hx
        rw [D.arcCarrier_eq_pieceOrder p] at hx
        rcases Set.mem_iUnion.mp hx with ⟨i, hxi⟩
        rcases List.getElem_of_mem i.2 with ⟨n, hn, hget⟩
        have hnL : n < L.length := by simpa [hL_len] using hn
        exact Set.mem_iUnion.2
          ⟨⟨n, hnL⟩, by
            rw [D.pieceCarrier_eq] at hxi
            simpa [L, Lidx, hget] using hxi⟩
      · intro hx
        rcases Set.mem_iUnion.mp hx with ⟨n, hxn⟩
        have hnidx : n.1 < Lidx.length := by simpa [hL_len] using n.2
        rw [D.arcCarrier_eq_pieceOrder p]
        exact Set.mem_iUnion.2
          ⟨⟨Lidx[n.1]'hnidx, hPiece_mem n.1 hnidx⟩, by
            rw [D.pieceCarrier_eq]
            simpa [L, Lidx] using hxn⟩
    have hhead :
        Lidx.head? = some (Lidx[0]'hLidx_pos) := by
      rw [List.head?_eq_getElem?]
      exact List.getElem?_eq_getElem hLidx_pos
    have hfirst : (L[0]'hL_pos).1 = p.1 := by
      have hs0 := D.arcPieceOrder_head_source p (Lidx[0]'hLidx_pos) hhead
      simpa [L, Lidx] using hs0
    have hlast_idx : Lidx.length - 1 < Lidx.length := Nat.sub_one_lt_of_lt hLidx_pos
    have hlast :
        Lidx.getLast? = some (Lidx[Lidx.length - 1]'hlast_idx) := by
      rw [List.getLast?_eq_getElem?]
      simp
    have hlast_target : (L[L.length - 1]'(Nat.sub_one_lt_of_lt hL_pos)).2 =
        (D.successor p).1 := by
      have hs_last :=
        D.arcPieceOrder_last_target p (Lidx[Lidx.length - 1]'hlast_idx) hlast
      have hlen_sub : L.length - 1 = Lidx.length - 1 := by omega
      simpa [L, Lidx, hlen_sub] using hs_last
    rw [hArc_as_L, hstraight, hfirst, hlast_target]
  have hContained :
      ∀ p : {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points},
        ∃ s : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2),
          s ∈ K.segments ∧
            segment ℝ p.1 (D.successor p).1 ⊆ segment ℝ s.1 s.2 := by
    intro p
    rcases
      FinitePolygonalSetCyclicArcCarrierContainedInListedSegment J K hKJ D p with
      ⟨s, hs, hArcSubset⟩
    refine ⟨s, hs, ?_⟩
    exact (convex_segment s.1 s.2).segment_subset
      (hArcSubset (D.arc_start_mem p)) (hArcSubset (D.arc_target_mem p))
  have hcarrier :
      J.carrier =
        ⋃ p : {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points},
          segment ℝ p.1 (D.successor p).1 := by
    apply le_antisymm
    · intro x hx
      rcases Set.mem_iUnion.mp (D.curve_covered_by_arcs hx) with ⟨p, hxp⟩
      exact Set.mem_iUnion.2 ⟨p, by simpa [hArcCarrier p] using hxp⟩
    · intro x hx
      rcases Set.mem_iUnion.mp hx with ⟨p, hxp⟩
      exact D.arc_in_curve p (by simpa [hArcCarrier p] using hxp)
  have hopen_subset :
      ∀ p : {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points},
        openSegment ℝ p.1 (D.successor p).1 ⊆ D.arcInterior p := by
    intro p x hx
    rw [D.arcInterior_eq p, hArcCarrier p]
    refine ⟨openSegment_subset_segment ℝ p.1 (D.successor p).1 hx, ?_⟩
    have hx_left : x ≠ p.1 := by
      intro h
      have hmem : p.1 ∈ openSegment ℝ p.1 (D.successor p).1 := by
        simpa [h] using hx
      exact D.successor_nondegenerate p
        ((left_mem_openSegment_iff (𝕜 := ℝ) (x := p.1) (y := (D.successor p).1)).1 hmem)
    have hx_right : x ≠ (D.successor p).1 := by
      intro h
      have hmem : (D.successor p).1 ∈ openSegment ℝ p.1 (D.successor p).1 := by
        simpa [h] using hx
      exact D.successor_nondegenerate p
        ((right_mem_openSegment_iff (𝕜 := ℝ) (x := p.1) (y := (D.successor p).1)).1 hmem)
    simp [hx_left, hx_right]
  have hno_listed_open :
      ∀ (p : {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points})
          (v : EuclideanSpace ℝ (Fin 2)),
        v ∈ K.points → v ∉ openSegment ℝ p.1 (D.successor p).1 := by
    intro p v hv hvin
    exact D.no_listed_point_in_arcInterior p v hv (hopen_subset p hvin)
  have hopen_disjoint :
      ∀ p q : {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points},
        p ≠ q →
          Disjoint (openSegment ℝ p.1 (D.successor p).1)
            (openSegment ℝ q.1 (D.successor q).1) := by
    intro p q hpq
    exact (D.arcInteriors_disjoint p q hpq).mono (hopen_subset p) (hopen_subset q)
  exact
    ⟨hcarrier, hContained, hArcCarrier, hopen_subset, hno_listed_open,
      hopen_disjoint⟩
