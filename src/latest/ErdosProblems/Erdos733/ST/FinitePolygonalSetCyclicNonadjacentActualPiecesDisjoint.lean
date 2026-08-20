import ErdosProblems.Erdos733.ST.SimpleClosedPolygonalCurve

open Classical
noncomputable section

-- [TABLET NODE: FinitePolygonalSetCyclicNonadjacentActualPiecesDisjoint]
lemma FinitePolygonalSetCyclicNonadjacentActualPiecesDisjoint
    (J : SimpleClosedPolygonalCurve)
    {PieceIndex : Type}
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
    (i j : PieceIndex)
    (hneq : pieceArc j ≠ pieceArc i)
    (hnot_succ : pieceArc j ≠ J.successor (pieceArc i))
    (hnot_pred : J.successor (pieceArc j) ≠ pieceArc i) :
    Disjoint (pieceCarrier i) (pieceCarrier j) := by
-- BODY
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
  have hdisj_arcs : Disjoint (pieceArc i).1.carrier (pieceArc j).1.carrier := by
    exact J.nonadjacent_disjoint (pieceArc i) (pieceArc j)
      hneq hnot_succ hnot_pred
  exact (Disjoint.mono (hpiece_subset_arc i) (hpiece_subset_arc j)) hdisj_arcs
