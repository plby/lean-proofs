import ErdosProblems.Erdos733.ST.SimpleClosedPolygonalCurve
import ErdosProblems.Erdos733.ST.FinitePolygonalSet

open Classical
noncomputable section

-- [TABLET NODE: CyclicCurvePresentation]
structure CyclicCurvePresentation (J : SimpleClosedPolygonalCurve) (K : FinitePolygonalSet) where
-- BODY
  vertices : Finset (EuclideanSpace ℝ (Fin 2))
  finite_set_carrier_eq : K.carrier = J.carrier
  vertices_eq_points :
    (vertices : Set (EuclideanSpace ℝ (Fin 2))) =
      (K.points : Set (EuclideanSpace ℝ (Fin 2)))
  vertices_nonempty : vertices.Nonempty
  vertices_on_curve :
    ∀ p : EuclideanSpace ℝ (Fin 2), p ∈ vertices → p ∈ J.carrier
  successor : Equiv.Perm {p : EuclideanSpace ℝ (Fin 2) // p ∈ vertices}
  successor_single_cycle :
    ∀ p q : {p : EuclideanSpace ℝ (Fin 2) // p ∈ vertices},
      ∃ n : ℕ, (successor^[n]) p = q
  successor_nondegenerate :
    ∀ p : {p : EuclideanSpace ℝ (Fin 2) // p ∈ vertices},
      p.1 ≠ (successor p).1
  cyclic_carrier_eq :
    J.carrier =
      ⋃ p : {p : EuclideanSpace ℝ (Fin 2) // p ∈ vertices},
        segment ℝ p.1 (successor p).1
  cyclic_piece_refines_segment :
    ∀ p : {p : EuclideanSpace ℝ (Fin 2) // p ∈ vertices},
      ∃ s : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2),
        s ∈ K.segments ∧
          segment ℝ p.1 (successor p).1 ⊆ segment ℝ s.1 s.2
  segment_refined_by_cyclic_pieces :
    ∀ s : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2),
      s ∈ K.segments →
        segment ℝ s.1 s.2 =
          ⋃ q : {q : {p : EuclideanSpace ℝ (Fin 2) // p ∈ vertices} //
              segment ℝ q.1 (successor q).1 ⊆ segment ℝ s.1 s.2},
            segment ℝ q.1.1 (successor q.1).1
  open_intersection_cardinality_partition :
    ∀ a b : EuclideanSpace ℝ (Fin 2),
      (∀ v : EuclideanSpace ℝ (Fin 2), v ∈ K.points → v ∉ openSegment ℝ a b) →
        (∀ s : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2),
          s ∈ K.segments →
            ¬ ∃ p q : EuclideanSpace ℝ (Fin 2),
              p ≠ q ∧ segment ℝ p q ⊆ segment ℝ a b ∩ segment ℝ s.1 s.2) →
        K.segments.sum (fun s =>
          Set.ncard (openSegment ℝ a b ∩ openSegment ℝ s.1 s.2)) =
          vertices.attach.sum fun p =>
            Set.ncard (openSegment ℝ a b ∩ openSegment ℝ p.1 (successor p).1)
  listed_segment_intersections_are_vertices :
    ∀ s t : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2),
      s ∈ K.segments → t ∈ K.segments → s ≠ t →
        ∀ p : EuclideanSpace ℝ (Fin 2),
          p ∈ segment ℝ s.1 s.2 → p ∈ segment ℝ t.1 t.2 → p ∈ vertices
