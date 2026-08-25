import Util.IncidenceGeometry.PolygonalPath

open Classical
noncomputable section

structure PolygonalPathRawStraightLineComplex (γ : PolygonalPath) where
  vertices : Finset (EuclideanSpace ℝ (Fin 2))
  edges : Finset (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2))
  original_vertices_mem :
    ∀ v : EuclideanSpace ℝ (Fin 2), v ∈ γ.vertices → v ∈ vertices
  source_mem : γ.source ∈ vertices
  target_mem : γ.target ∈ vertices
  edge_source_mem :
    ∀ e : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2),
      e ∈ edges → e.1 ∈ vertices
  edge_target_mem :
    ∀ e : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2),
      e ∈ edges → e.2 ∈ vertices
  edge_nondegenerate :
    ∀ e : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2),
      e ∈ edges → e.1 ≠ e.2
  edge_refines_path_segment :
    ∀ e : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2),
      e ∈ edges →
        ∃ i : ℕ, ∃ hi : i + 1 < γ.vertices.length,
          segment ℝ e.1 e.2 ⊆ segment ℝ γ.vertices[i] γ.vertices[i + 1]
  edge_subset_carrier :
    ∀ e : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2),
      e ∈ edges → segment ℝ e.1 e.2 ⊆ γ.carrier
  no_vertex_in_edge_interior :
    ∀ e : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2),
      e ∈ edges →
        ∀ v : EuclideanSpace ℝ (Fin 2),
          v ∈ vertices → v ∉ openSegment ℝ e.1 e.2
  distinct_edges_meet_at_common_endpoints :
    ∀ e f : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2),
      e ∈ edges → f ∈ edges → e ≠ f →
        segment ℝ e.1 e.2 ∩ segment ℝ f.1 f.2 =
          ({e.1, e.2} : Set (EuclideanSpace ℝ (Fin 2))) ∩
            ({f.1, f.2} : Set (EuclideanSpace ℝ (Fin 2)))
  rawWalk : List (EuclideanSpace ℝ (Fin 2))
  rawWalk_head : rawWalk.head? = some γ.source
  rawWalk_last : rawWalk.getLast? = some γ.target
  rawWalk_length_ge_two : γ.source ≠ γ.target → 2 ≤ rawWalk.length
  rawWalk_vertices_mem :
    ∀ v : EuclideanSpace ℝ (Fin 2), v ∈ rawWalk → v ∈ vertices
  rawWalk_steps :
    ∀ i : ℕ, (hi : i + 1 < rawWalk.length) →
      (rawWalk[i], rawWalk[i + 1]) ∈ edges ∨
        (rawWalk[i + 1], rawWalk[i]) ∈ edges

