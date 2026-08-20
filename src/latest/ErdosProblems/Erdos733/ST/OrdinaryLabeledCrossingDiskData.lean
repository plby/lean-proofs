import ErdosProblems.Erdos733.ST.OrdinaryCrossingLocalBranchData
import ErdosProblems.Erdos733.ST.OrdinaryPolygonalDrawing

open Classical
noncomputable section

-- [TABLET NODE: OrdinaryLabeledCrossingDiskData]
structure OrdinaryLabeledCrossingDiskData {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet]
    (D : OrdinaryPolygonalDrawing G) (x : {p // p ∈ D.crossingSet}) where
-- BODY
  firstEdge : G.edgeFinset
  secondEdge : G.edgeFinset
  edges_ne : firstEdge ≠ secondEdge
  center_first : x.1 ∈ (D.edgeArc firstEdge).relativeInterior
  center_second : x.1 ∈ (D.edgeArc secondEdge).relativeInterior
  owner_labels :
    ∀ e : G.edgeFinset,
      x.1 ∈ (D.edgeArc e).relativeInterior → e = firstEdge ∨ e = secondEdge
  radius : ℝ
  firstBranch : OrdinaryCrossingLocalBranchData (D.edgeArc firstEdge) x.1 radius
  secondBranch : OrdinaryCrossingLocalBranchData (D.edgeArc secondEdge) x.1 radius
  no_vertex_in_closedBall :
    ∀ v : V, D.vertexPlacement v ∉ Metric.closedBall x.1 radius
  no_other_crossing_in_closedBall :
    ∀ y : {p // p ∈ D.crossingSet},
      y ≠ x → y.1 ∉ Metric.closedBall x.1 radius
  exact_local_drawing_carrier :
    Metric.closedBall x.1 radius ∩
        (⋃ e : G.edgeFinset, (D.edgeArc e).carrier) =
      Metric.closedBall x.1 radius ∩
        ((D.edgeArc firstEdge).carrier ∪ (D.edgeArc secondEdge).carrier)
  pair_meets_only_at_center :
    ∀ ⦃q : EuclideanSpace ℝ (Fin 2)⦄,
      q ∈ Metric.closedBall x.1 radius →
        q ∈ (D.edgeArc firstEdge).relativeInterior →
          q ∈ (D.edgeArc secondEdge).relativeInterior → q = x.1
  firstTransverseIndex : ℕ
  secondTransverseIndex : ℕ
  firstTransverseIndex_valid :
    firstTransverseIndex + 1 < (D.edgeArc firstEdge).vertices.length
  secondTransverseIndex_valid :
    secondTransverseIndex + 1 < (D.edgeArc secondEdge).vertices.length
  firstTransverseIndex_local :
    firstTransverseIndex = firstBranch.beforeIndex ∨
      firstTransverseIndex = firstBranch.afterIndex
  secondTransverseIndex_local :
    secondTransverseIndex = secondBranch.beforeIndex ∨
      secondTransverseIndex = secondBranch.afterIndex
  some_germs_transverse :
    ¬ ∃ c : ℝ,
      (D.edgeArc secondEdge).vertices.get
            ⟨secondTransverseIndex + 1, secondTransverseIndex_valid⟩ -
          (D.edgeArc secondEdge).vertices.get
            ⟨secondTransverseIndex,
              Nat.lt_trans (Nat.lt_succ_self _) secondTransverseIndex_valid⟩ =
        c • ((D.edgeArc firstEdge).vertices.get
              ⟨firstTransverseIndex + 1, firstTransverseIndex_valid⟩ -
            (D.edgeArc firstEdge).vertices.get
              ⟨firstTransverseIndex,
                Nat.lt_trans (Nat.lt_succ_self _) firstTransverseIndex_valid⟩)
  local_germs_share_no_nondegenerate_subarc :
    ¬ ∃ i j : ℕ,
      ∃ (hi : i + 1 < (D.edgeArc firstEdge).vertices.length)
        (hj : j + 1 < (D.edgeArc secondEdge).vertices.length),
          (i = firstBranch.beforeIndex ∨ i = firstBranch.afterIndex) ∧
            (j = secondBranch.beforeIndex ∨ j = secondBranch.afterIndex) ∧
              ∃ p q : EuclideanSpace ℝ (Fin 2),
                p ≠ q ∧
                  segment ℝ p q ⊆
                    segment ℝ
                        (D.edgeArc firstEdge).vertices[i]
                        (D.edgeArc firstEdge).vertices[i + 1] ∩
                      segment ℝ
                        (D.edgeArc secondEdge).vertices[j]
                        (D.edgeArc secondEdge).vertices[j + 1]
  first_before_ne_second_before :
    firstBranch.beforeGate ≠ secondBranch.beforeGate
  first_before_ne_second_after :
    firstBranch.beforeGate ≠ secondBranch.afterGate
  first_after_ne_second_before :
    firstBranch.afterGate ≠ secondBranch.beforeGate
  first_after_ne_second_after :
    firstBranch.afterGate ≠ secondBranch.afterGate
