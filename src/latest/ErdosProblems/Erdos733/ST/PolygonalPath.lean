import ErdosProblems.Erdos733.ST.Preamble

-- [TABLET NODE: PolygonalPath]
structure PolygonalPath where
-- BODY
  vertices : List (EuclideanSpace ℝ (Fin 2))
  vertices_nonempty : vertices ≠ []
  source : EuclideanSpace ℝ (Fin 2)
  target : EuclideanSpace ℝ (Fin 2)
  source_eq_head : vertices.head? = some source
  target_eq_last : vertices.getLast? = some target
  carrier : Set (EuclideanSpace ℝ (Fin 2))
  carrier_eq :
    carrier =
      ({source, target} : Set (EuclideanSpace ℝ (Fin 2))) ∪
        {p | ∃ i : ℕ, ∃ hi : i + 1 < vertices.length,
          p ∈ segment ℝ vertices[i] vertices[i + 1]}
