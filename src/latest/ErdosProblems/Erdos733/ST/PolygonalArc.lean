import ErdosProblems.Erdos733.ST.Preamble

-- [TABLET NODE: PolygonalArc]
structure PolygonalArc where
-- BODY
  vertices : List (EuclideanSpace ℝ (Fin 2))
  length_ge_two : 2 ≤ vertices.length
  source : EuclideanSpace ℝ (Fin 2)
  target : EuclideanSpace ℝ (Fin 2)
  source_eq_head : vertices.head? = some source
  target_eq_last : vertices.getLast? = some target
  carrier : Set (EuclideanSpace ℝ (Fin 2))
  relativeInterior : Set (EuclideanSpace ℝ (Fin 2))
  carrier_eq :
    carrier =
      {p | ∃ i : ℕ, ∃ hi : i + 1 < vertices.length,
        p ∈ segment ℝ vertices[i] vertices[i + 1]}
  relativeInterior_eq : relativeInterior = carrier \ ({source, target} : Set (EuclideanSpace ℝ (Fin 2)))
  simple_vertices : vertices.Nodup
  segment_intersections :
    ∀ ⦃i j : ℕ⦄,
      (hi : i + 1 < vertices.length) →
      (hj : j + 1 < vertices.length) →
      i < j →
      (segment ℝ vertices[i] vertices[i + 1] ∩
          segment ℝ vertices[j] vertices[j + 1]) =
        if j = i + 1 then {vertices[j]} else ∅
  vertices_avoid_nonincident_interiors :
    ∀ ⦃i k : ℕ⦄,
      (hi : i + 1 < vertices.length) →
      (hk : k < vertices.length) →
      k ≠ i →
      k ≠ i + 1 →
      vertices[k] ∉ openSegment ℝ vertices[i] vertices[i + 1]
