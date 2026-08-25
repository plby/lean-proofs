import Util.IncidenceGeometry.IsAffineLine
import Util.IncidenceGeometry.LineIncidences

open Classical
noncomputable section

structure PointLineConsecutivePairGraphData
    (P : Finset (EuclideanSpace ℝ (Fin 2)))
    (L : Finset {ell : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2)) //
      IsAffineLine ell}) where
  retainedLines : Finset {ell : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2)) //
    IsAffineLine ell}
  retainedLines_subset : retainedLines ⊆ L
  retainedLine_incident : ∀ ell ∈ retainedLines,
    ∃ p : P, (p.1 : EuclideanSpace ℝ (Fin 2)) ∈
      (ell.1 : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2)))
  graph : SimpleGraph P
  edgeOwner : graph.edgeFinset → retainedLines
  edgeSourceVertex : graph.edgeFinset → P
  edgeTargetVertex : graph.edgeFinset → P
  edge_adjacent : ∀ e, graph.Adj (edgeSourceVertex e) (edgeTargetVertex e)
  edge_eq_mk : ∀ e, e.1 = Sym2.mk (edgeSourceVertex e) (edgeTargetVertex e)
  edge_source_on_owner : ∀ e,
    (edgeSourceVertex e).1 ∈
      ((edgeOwner e).1.1 : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2)))
  edge_target_on_owner : ∀ e,
    (edgeTargetVertex e).1 ∈
      ((edgeOwner e).1.1 : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2)))
  edge_no_point_in_openSegment : ∀ (e : graph.edgeFinset) (p : P),
    p.1 ∉ openSegment ℝ (edgeSourceVertex e).1 (edgeTargetVertex e).1
  same_owner_openSegment_disjoint : ∀ e₁ e₂ : graph.edgeFinset,
    e₁ ≠ e₂ → edgeOwner e₁ = edgeOwner e₂ →
      Disjoint
        (openSegment ℝ (edgeSourceVertex e₁).1 (edgeTargetVertex e₁).1)
        (openSegment ℝ (edgeSourceVertex e₂).1 (edgeTargetVertex e₂).1)
  same_owner_segment_intersection_subsingleton : ∀ e₁ e₂ : graph.edgeFinset,
    e₁ ≠ e₂ → edgeOwner e₁ = edgeOwner e₂ →
      (segment ℝ (edgeSourceVertex e₁).1 (edgeTargetVertex e₁).1 ∩
        segment ℝ (edgeSourceVertex e₂).1 (edgeTargetVertex e₂).1).Subsingleton
  incidence_eq :
    LineIncidences P L = graph.edgeFinset.card + retainedLines.card
