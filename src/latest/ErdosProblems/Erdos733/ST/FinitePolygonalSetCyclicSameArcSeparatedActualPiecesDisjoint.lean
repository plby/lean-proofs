import ErdosProblems.Erdos733.ST.SimpleClosedPolygonalCurve

open Classical
noncomputable section

-- [TABLET NODE: FinitePolygonalSetCyclicSameArcSeparatedActualPiecesDisjoint]
lemma FinitePolygonalSetCyclicSameArcSeparatedActualPiecesDisjoint
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
    (hsame : pieceArc i = pieceArc j)
    (hgap : (pieceSegmentIndex i).1 + 1 < (pieceSegmentIndex j).1) :
    Disjoint (pieceCarrier i) (pieceCarrier j) := by
-- BODY
  let γ : PolygonalArc := (pieceArc i).1
  let a : ℕ := (pieceSegmentIndex i).1
  let b : ℕ := (pieceSegmentIndex j).1
  have hi : a + 1 < γ.vertices.length := by
    simpa [γ, a] using (pieceSegmentIndex i).2
  have hj : b + 1 < γ.vertices.length := by
    simpa [γ, b, hsame] using (pieceSegmentIndex j).2
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
  have hparent_empty :
      segment ℝ (γ.vertices[a]'(Nat.lt_of_succ_lt hi)) (γ.vertices[a + 1]'hi) ∩
          segment ℝ (γ.vertices[b]'(Nat.lt_of_succ_lt hj)) (γ.vertices[b + 1]'hj) =
        (∅ : Set (EuclideanSpace ℝ (Fin 2))) := by
    have hab : a + 1 < b := by
      simpa [a, b] using hgap
    have hinter := γ.segment_intersections hi hj (by omega)
    have hnot_adj : b ≠ a + 1 := by omega
    simpa [hnot_adj] using hinter
  rw [Set.disjoint_left]
  intro x hxi hxj
  have hxi_parent :
      x ∈ segment ℝ (γ.vertices[a]'(Nat.lt_of_succ_lt hi))
          (γ.vertices[a + 1]'hi) := by
    simpa [γ, a] using hpiece_subset_parent i hxi
  have hxj_parent :
      x ∈ segment ℝ (γ.vertices[b]'(Nat.lt_of_succ_lt hj))
          (γ.vertices[b + 1]'hj) := by
    simpa [γ, b, hsame] using hpiece_subset_parent j hxj
  have hx_inter :
      x ∈ segment ℝ (γ.vertices[a]'(Nat.lt_of_succ_lt hi))
            (γ.vertices[a + 1]'hi) ∩
          segment ℝ (γ.vertices[b]'(Nat.lt_of_succ_lt hj))
            (γ.vertices[b + 1]'hj) :=
    ⟨hxi_parent, hxj_parent⟩
  rw [hparent_empty] at hx_inter
  exact hx_inter
