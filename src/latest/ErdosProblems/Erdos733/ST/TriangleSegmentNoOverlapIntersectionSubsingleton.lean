import ErdosProblems.Erdos733.ST.Preamble

open Classical
noncomputable section

-- [TABLET NODE: TriangleSegmentNoOverlapIntersectionSubsingleton]
lemma TriangleSegmentNoOverlapIntersectionSubsingleton
    (x y u v : EuclideanSpace ℝ (Fin 2))
    (hNoOverlap :
      ¬ ∃ p q : EuclideanSpace ℝ (Fin 2),
        p ≠ q ∧ segment ℝ p q ⊆ segment ℝ x y ∩ segment ℝ u v) :
    (segment ℝ x y ∩ segment ℝ u v : Set (EuclideanSpace ℝ (Fin 2))).Subsingleton ∧
      Set.Finite (openSegment ℝ x y ∩ openSegment ℝ u v :
        Set (EuclideanSpace ℝ (Fin 2))) := by
-- BODY
  have hclosed :
      (segment ℝ x y ∩ segment ℝ u v :
        Set (EuclideanSpace ℝ (Fin 2))).Subsingleton := by
    intro p hp q hq
    by_contra hpq
    exact hNoOverlap ⟨p, q, hpq, by
      intro r hr
      exact ⟨(convex_segment x y).segment_subset hp.1 hq.1 hr,
        (convex_segment u v).segment_subset hp.2 hq.2 hr⟩⟩
  constructor
  · exact hclosed
  · have hsub :
        (openSegment ℝ x y ∩ openSegment ℝ u v :
          Set (EuclideanSpace ℝ (Fin 2))) ⊆
          segment ℝ x y ∩ segment ℝ u v := by
      intro p hp
      exact ⟨openSegment_subset_segment ℝ x y hp.1,
        openSegment_subset_segment ℝ u v hp.2⟩
    exact hclosed.finite.subset hsub
