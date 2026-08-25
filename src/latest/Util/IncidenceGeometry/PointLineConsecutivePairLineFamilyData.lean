import Util.IncidenceGeometry.IsAffineLine

open Classical
noncomputable section

structure PointLineConsecutivePairLineFamilyData
    (P : Finset (EuclideanSpace ℝ (Fin 2)))
    (L : Finset {ell : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2)) //
      IsAffineLine ell}) where
  retainedLines : Finset {ell : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2)) //
    IsAffineLine ell}
  retainedLines_mem_iff : ∀ ell,
    ell ∈ retainedLines ↔ ell ∈ L ∧
      ∃ p : P, (p.1 : EuclideanSpace ℝ (Fin 2)) ∈
        (ell.1 : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2)))
  coordinate : retainedLines → EuclideanSpace ℝ (Fin 2) → ℝ
  coordinate_injective_on_line : ∀ (ell : retainedLines) {x y},
    x ∈ (ell.1.1 : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2))) →
    y ∈ (ell.1.1 : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2))) →
    coordinate ell x = coordinate ell y → x = y
  coordinate_affineCombination : ∀ (ell : retainedLines) {x y},
    x ∈ (ell.1.1 : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2))) →
    y ∈ (ell.1.1 : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2))) →
    ∀ t : ℝ,
      coordinate ell ((1 - t) • x + t • y) =
        (1 - t) * coordinate ell x + t * coordinate ell y
  localEdges : retainedLines → Finset (P × P)
  localEdges_mem_iff : ∀ (ell : retainedLines) (p q : P),
    (p, q) ∈ localEdges ell ↔
      (p.1 : EuclideanSpace ℝ (Fin 2)) ∈
          (ell.1.1 : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2))) ∧
        (q.1 : EuclideanSpace ℝ (Fin 2)) ∈
          (ell.1.1 : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2))) ∧
        coordinate ell p.1 < coordinate ell q.1 ∧
        ∀ r : P,
          (r.1 : EuclideanSpace ℝ (Fin 2)) ∈
              (ell.1.1 : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2))) →
          ¬(coordinate ell p.1 < coordinate ell r.1 ∧
            coordinate ell r.1 < coordinate ell q.1)
  localEdge_no_point_in_openSegment : ∀ (ell : retainedLines)
      (e : P × P), e ∈ localEdges ell → ∀ p : P,
    p.1 ∉ openSegment ℝ e.1.1 e.2.1
  distinct_localEdges_openSegment_disjoint : ∀ (ell : retainedLines)
      (e₁ e₂ : P × P), e₁ ∈ localEdges ell → e₂ ∈ localEdges ell →
      e₁ ≠ e₂ →
    Disjoint (openSegment ℝ e₁.1.1 e₁.2.1)
      (openSegment ℝ e₂.1.1 e₂.2.1)
  distinct_localEdges_segment_intersection_subsingleton :
    ∀ (ell : retainedLines) (e₁ e₂ : P × P),
      e₁ ∈ localEdges ell → e₂ ∈ localEdges ell → e₁ ≠ e₂ →
      (segment ℝ e₁.1.1 e₁.2.1 ∩ segment ℝ e₂.1.1 e₂.2.1).Subsingleton
  localEdges_card_add_one : ∀ ell : retainedLines,
    (localEdges ell).card + 1 =
      (P.filter fun p =>
        p ∈
          (ell.1.1 : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2)))).card
