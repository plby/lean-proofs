import Util.IncidenceGeometry.Basic

structure FinitePolygonalSet where
  carrier : Set (EuclideanSpace ℝ (Fin 2))
  points : Finset (EuclideanSpace ℝ (Fin 2))
  segments : Finset (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2))
  segment_nondegenerate :
    ∀ s : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2),
      s ∈ segments → s.1 ≠ s.2
  segment_endpoints_listed :
    ∀ s : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2),
      s ∈ segments → s.1 ∈ points ∧ s.2 ∈ points
  segment_intersections_listed :
    ∀ s t : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2),
      s ∈ segments → t ∈ segments → s ≠ t →
        ∀ p : EuclideanSpace ℝ (Fin 2),
          p ∈ segment ℝ s.1 s.2 → p ∈ segment ℝ t.1 t.2 → p ∈ points
  carrier_eq :
    carrier =
      (points : Set (EuclideanSpace ℝ (Fin 2))) ∪
        ⋃ s : {s // s ∈ segments}, segment ℝ s.1.1 s.1.2
