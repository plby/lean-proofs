import Util.IncidenceGeometry.FinitePolygonalSetCyclicTraversalCuts

open Classical
noncomputable section

lemma FinitePolygonalSetCyclicAdjacentPiecesSameListedSegment
    (J : SimpleClosedPolygonalCurve) (K : FinitePolygonalSet)
    (D : FinitePolygonalSetCyclicTraversalCuts J K)
    (p : {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points})
    (n : ℕ) (hn : n + 1 < (D.arcPieceOrder p).length)
    (s t : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2))
    (hs : s ∈ K.segments) (ht : t ∈ K.segments)
    (hleft :
      D.pieceCarrier ((D.arcPieceOrder p)[n]) ⊆ segment ℝ s.1 s.2)
    (hright :
      D.pieceCarrier ((D.arcPieceOrder p)[n + 1]) ⊆ segment ℝ t.1 t.2) :
    s = t := by
  by_contra hst
  let a : D.pieceIndex := (D.arcPieceOrder p)[n]
  let b : D.pieceIndex := (D.arcPieceOrder p)[n + 1]
  have hjunction : D.pieceTarget a = D.pieceSource b := by
    simpa [a, b] using (D.arcPieceOrder_consecutive p n hn).1
  have htarget_mem : D.pieceTarget a ∈ D.pieceCarrier a := by
    rw [D.pieceCarrier_eq a]
    exact right_mem_segment ℝ (D.pieceSource a) (D.pieceTarget a)
  have hsource_mem : D.pieceSource b ∈ D.pieceCarrier b := by
    rw [D.pieceCarrier_eq b]
    exact left_mem_segment ℝ (D.pieceSource b) (D.pieceTarget b)
  have hxs : D.pieceTarget a ∈ segment ℝ s.1 s.2 := by
    exact hleft (by simpa [a] using htarget_mem)
  have hxt : D.pieceTarget a ∈ segment ℝ t.1 t.2 := by
    have hsource_t : D.pieceSource b ∈ segment ℝ t.1 t.2 := by
      exact hright (by simpa [b] using hsource_mem)
    simpa [hjunction] using hsource_t
  have hlisted : D.pieceTarget a ∈ K.points :=
    K.segment_intersections_listed s t hs ht hst (D.pieceTarget a) hxs hxt
  have hinterior : D.pieceTarget a ∈ D.arcInterior p := by
    simpa [a] using D.ordered_consecutive_junction_mem_arcInterior p n hn
  exact D.no_listed_point_in_arcInterior p (D.pieceTarget a) hlisted hinterior
