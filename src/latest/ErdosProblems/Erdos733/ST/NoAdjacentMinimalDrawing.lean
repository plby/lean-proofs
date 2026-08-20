import ErdosProblems.Erdos733.ST.AdjacentEdgeTailFreeReroute
import ErdosProblems.Erdos733.ST.CrossingNumber
import ErdosProblems.Erdos733.ST.NatSInfRangeAttained
import ErdosProblems.Erdos733.ST.OrdinaryPolygonalDrawingNonempty

open Classical
noncomputable section

-- [TABLET NODE: NoAdjacentMinimalDrawing]
lemma NoAdjacentMinimalDrawing {V : Type*} [Fintype V] (G : SimpleGraph V)
    [Fintype G.edgeSet] :
    ∃ D : OrdinaryPolygonalDrawing G,
      D.crossingSet.card = CrossingNumber G ∧ D.adjacentEdgeCrossingCount = 0 := by
-- BODY
  have hnonempty : Nonempty (OrdinaryPolygonalDrawing G) :=
    OrdinaryPolygonalDrawingNonempty G
  have hattainment :
      ∃ D : OrdinaryPolygonalDrawing G,
        D.crossingSet.card = CrossingNumber G ∧
          ∀ E : OrdinaryPolygonalDrawing G,
            CrossingNumber G ≤ E.crossingSet.card := by
    simpa [CrossingNumber] using
      (NatSInfRangeAttained
        (α := OrdinaryPolygonalDrawing G)
        (fun E : OrdinaryPolygonalDrawing G => E.crossingSet.card)
        hnonempty)
  rcases hattainment with ⟨D, ⟨hDmin, hminimal⟩⟩
  refine ⟨D, hDmin, ?_⟩
  by_contra hadj
  rw [D.adjacentEdgeCrossingCount_eq] at hadj
  obtain ⟨x, hx⟩ := Finset.card_ne_zero.mp hadj
  rw [Finset.mem_filter] at hx
  rcases hx with ⟨hxCross, alpha, beta, hab, ⟨u, hua, hub⟩, hxa, hxb⟩
  obtain ⟨D', hdecrease⟩ :=
    AdjacentEdgeTailFreeReroute G D alpha beta u hab hua hub
      ⟨x, hxCross, hxa, hxb⟩
  have hlower := hminimal D'
  omega
