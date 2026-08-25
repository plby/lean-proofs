import Util.IncidenceGeometry.FinitePolygonalSetCyclicPieceFiniteDeletionDense

open Classical
noncomputable section

lemma FinitePolygonalSetCyclicOrderedPieceCoveredByListedSegments
    (J : SimpleClosedPolygonalCurve) (K : FinitePolygonalSet)
    (hKJ : K.carrier = J.carrier)
    (D : FinitePolygonalSetCyclicTraversalCuts J K)
    (p : {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points})
    (i : D.pieceIndex) (hi : i ∈ D.arcPieceOrder p) :
    D.pieceCarrier i ⊆
      ⋃ s : {s // s ∈ K.segments}, segment ℝ s.1.1 s.1.2 := by
  let U : Set (EuclideanSpace ℝ (Fin 2)) :=
    ⋃ s : {s // s ∈ K.segments}, segment ℝ s.1.1 s.1.2
  have hU_def :
      U = ⋃ s : {s // s ∈ K.segments}, segment ℝ s.1.1 s.1.2 := rfl
  have hclosed_segment :
      ∀ a b : EuclideanSpace ℝ (Fin 2), IsClosed (segment ℝ a b) := by
    intro a b
    rw [segment_eq_image_lineMap]
    exact (isCompact_Icc.image AffineMap.lineMap_continuous).isClosed
  have hU_closed : IsClosed U := by
    rw [hU_def]
    exact isClosed_iUnion_of_finite fun s => hclosed_segment s.1.1 s.1.2
  have hnonlisted_subset :
      D.pieceCarrier i \ (K.points : Set (EuclideanSpace ℝ (Fin 2))) ⊆ U := by
    intro x hx
    rcases hx with ⟨hxpiece, hxnot⟩
    have hxArc : x ∈ D.arcCarrier p := by
      rw [D.arcCarrier_eq_pieceOrder p]
      exact Set.mem_iUnion.2 ⟨⟨i, hi⟩, hxpiece⟩
    have hxJ : x ∈ J.carrier := D.arc_in_curve p hxArc
    have hxK : x ∈ K.carrier := by
      simpa [hKJ] using hxJ
    rw [K.carrier_eq] at hxK
    rcases hxK with hxpoint | hxseg
    · exact False.elim (hxnot hxpoint)
    · simpa [hU_def] using hxseg
  intro x hxpiece
  have hxclosure : x ∈ closure U :=
    closure_mono hnonlisted_subset
      (FinitePolygonalSetCyclicPieceFiniteDeletionDense J K D i hxpiece)
  have hxU : x ∈ U := by
    simpa [hU_closed.closure_eq] using hxclosure
  simpa [hU_def] using hxU
