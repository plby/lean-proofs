import ErdosProblems.Erdos733.ST.PolygonalArc

open Classical
noncomputable section

-- [TABLET NODE: OrdinaryCleanLocalCrossing]
structure OrdinaryCleanLocalCrossing {ι : Type*} (Γ : ι → PolygonalArc)
    (i j : ι) (p : EuclideanSpace ℝ (Fin 2)) where
-- BODY
  firstIndex : ℕ
  secondIndex : ℕ
  firstIndex_valid : firstIndex + 1 < (Γ i).vertices.length
  secondIndex_valid : secondIndex + 1 < (Γ j).vertices.length
  first_open :
    p ∈ openSegment ℝ (Γ i).vertices[firstIndex] (Γ i).vertices[firstIndex + 1]
  second_open :
    p ∈ openSegment ℝ (Γ j).vertices[secondIndex] (Γ j).vertices[secondIndex + 1]
  first_not_vertex : p ∉ (Γ i).vertices
  second_not_vertex : p ∉ (Γ j).vertices
  directions_nonparallel :
    ¬ ∃ t : ℝ,
      (Γ j).vertices[secondIndex + 1] - (Γ j).vertices[secondIndex] =
        t • ((Γ i).vertices[firstIndex + 1] - (Γ i).vertices[firstIndex])
  pair_unique :
    ∀ ⦃q : EuclideanSpace ℝ (Fin 2)⦄,
      q ∈ (Γ i).relativeInterior → q ∈ (Γ j).relativeInterior → q = p
  radius : ℝ
  radius_pos : 0 < radius
  two_branch_neighborhood :
    Metric.ball p radius ∩ (⋃ k, (Γ k).carrier) =
      Metric.ball p radius ∩
        (segment ℝ (Γ i).vertices[firstIndex] (Γ i).vertices[firstIndex + 1] ∪
          segment ℝ (Γ j).vertices[secondIndex] (Γ j).vertices[secondIndex + 1])
