import ErdosProblems.Erdos733.ST.Preamble
import Mathlib.Analysis.InnerProductSpace.Convex

open Classical
noncomputable section

-- [TABLET NODE: EndpointUnitDiskChordSubsegmentUnitContainment]
lemma EndpointUnitDiskChordSubsegmentUnitContainment
    {A B X Y : EuclideanSpace ℝ (Fin 2)}
    (hA : dist A (0 : EuclideanSpace ℝ (Fin 2)) = 1)
    (hB : dist B (0 : EuclideanSpace ℝ (Fin 2)) = 1)
    (hAB : A ≠ B)
    (hX : X ∈ segment ℝ A B)
    (hY : Y ∈ segment ℝ A B) :
    segment ℝ X Y ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 ∧
      ∀ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
        p ∈ segment ℝ X Y → p ≠ A → p ≠ B →
          p ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
-- BODY
  have hA_closed : A ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
    simp [Metric.mem_closedBall, hA]
  have hB_closed : B ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
    simp [Metric.mem_closedBall, hB]
  have hX_closed : X ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 :=
    (convex_closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1).segment_subset
      hA_closed hB_closed hX
  have hY_closed : Y ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 :=
    (convex_closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1).segment_subset
      hA_closed hB_closed hY
  constructor
  · exact (convex_closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1).segment_subset
      hX_closed hY_closed
  · intro p hp hpA hpB
    have hp_segmentAB : p ∈ segment ℝ A B :=
      (convex_segment A B).segment_subset hX hY hp
    exact openSegment_subset_ball_of_ne hA_closed hB_closed hAB
      (mem_openSegment_of_ne_left_right hpA.symm hpB.symm hp_segmentAB)
