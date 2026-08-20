import ErdosProblems.Erdos733.ST.OrdinaryCleanLocalCrossing
import ErdosProblems.Erdos733.ST.OrdinaryLabeledCrossingDiskFamily

open Classical
noncomputable section

-- [TABLET NODE: OrdinaryLabeledCrossingDiskFillingFamily]
structure OrdinaryLabeledCrossingDiskFillingFamily {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet]
    (D : OrdinaryPolygonalDrawing G)
    (F : OrdinaryLabeledCrossingDiskFamily G D) where
-- BODY
  ownerEdge : {p // p ∈ D.crossingSet} → Fin 2 → G.edgeFinset
  fillingArc : {p // p ∈ D.crossingSet} → Fin 2 → PolygonalArc
  owner_zero :
    ∀ x, ownerEdge x 0 = (F.disk x).firstEdge
  owner_one :
    ∀ x, ownerEdge x 1 = (F.disk x).secondEdge
  source_zero :
    ∀ x, (fillingArc x 0).source = (F.disk x).firstBranch.beforeGate
  target_zero :
    ∀ x, (fillingArc x 0).target = (F.disk x).firstBranch.afterGate
  source_one :
    ∀ x, (fillingArc x 1).source = (F.disk x).secondBranch.beforeGate
  target_one :
    ∀ x, (fillingArc x 1).target = (F.disk x).secondBranch.afterGate
  carrier_subset_closedBall :
    ∀ x i,
      (fillingArc x i).carrier ⊆ Metric.closedBall x.1 (F.disk x).radius
  relativeInterior_subset_ball :
    ∀ x i,
      (fillingArc x i).relativeInterior ⊆ Metric.ball x.1 (F.disk x).radius
  no_shared_nondegenerate_subarc :
    ∀ x,
      ¬ ∃ m n : ℕ,
        ∃ (hm : m + 1 < (fillingArc x 0).vertices.length)
          (hn : n + 1 < (fillingArc x 1).vertices.length),
          ∃ p q : EuclideanSpace ℝ (Fin 2),
            p ≠ q ∧
              segment ℝ p q ⊆
                segment ℝ (fillingArc x 0).vertices[m]
                    (fillingArc x 0).vertices[m + 1] ∩
                  segment ℝ (fillingArc x 1).vertices[n]
                    (fillingArc x 1).vertices[n + 1]
  pair_meets_at_most_once :
    ∀ x ⦃p q : EuclideanSpace ℝ (Fin 2)⦄,
      p ∈ (fillingArc x 0).relativeInterior →
        p ∈ (fillingArc x 1).relativeInterior →
          q ∈ (fillingArc x 0).relativeInterior →
            q ∈ (fillingArc x 1).relativeInterior → p = q
  crossing_open_segments :
    ∀ x ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
      p ∈ (fillingArc x 0).relativeInterior →
        p ∈ (fillingArc x 1).relativeInterior →
          ∃ m n : ℕ,
            ∃ (hm : m + 1 < (fillingArc x 0).vertices.length)
              (hn : n + 1 < (fillingArc x 1).vertices.length),
              p ∈ openSegment ℝ (fillingArc x 0).vertices[m]
                    (fillingArc x 0).vertices[m + 1] ∧
                p ∈ openSegment ℝ (fillingArc x 1).vertices[n]
                    (fillingArc x 1).vertices[n + 1] ∧
                  ¬ ∃ t : ℝ,
                    (fillingArc x 1).vertices[n + 1] -
                        (fillingArc x 1).vertices[n] =
                      t • ((fillingArc x 0).vertices[m + 1] -
                        (fillingArc x 0).vertices[m])
  clean_crossing :
    ∀ x ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
      p ∈ (fillingArc x 0).relativeInterior →
        p ∈ (fillingArc x 1).relativeInterior →
          Nonempty (OrdinaryCleanLocalCrossing (fillingArc x) 0 1 p)
