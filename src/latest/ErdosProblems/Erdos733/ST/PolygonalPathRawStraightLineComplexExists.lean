import ErdosProblems.Erdos733.ST.PolygonalPathPairwiseCutVertexSetExists
import ErdosProblems.Erdos733.ST.PolygonalPathRawStraightLineComplex
import ErdosProblems.Erdos733.ST.PolygonalPathRetainedElementaryEdgesExists
import ErdosProblems.Erdos733.ST.PolygonalPathRetainedElementaryEdgesDistinctMeetAtCommonEndpoints
import ErdosProblems.Erdos733.ST.PolygonalPathRetainedElementaryRawWalkExists

open Classical
noncomputable section

-- [TABLET NODE: PolygonalPathRawStraightLineComplexExists]
lemma PolygonalPathRawStraightLineComplexExists (γ : PolygonalPath) :
    Nonempty (PolygonalPathRawStraightLineComplex γ) := by
-- BODY
  rcases PolygonalPathPairwiseCutVertexSetExists γ with
    ⟨cutVertices, hcut_original, hcut_finite_pair, hcut_infinite_pair⟩
  rcases PolygonalPathRetainedElementaryEdgesExists γ cutVertices hcut_original with
    ⟨retainedEdgesData⟩
  have retained_no_cut_open :
      ∀ e : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2),
        e ∈ retainedEdgesData.retainedEdges →
          ∀ v : EuclideanSpace ℝ (Fin 2),
            v ∈ cutVertices → v ∉ openSegment ℝ e.1 e.2 :=
    by
      intro e he v hv
      rcases retainedEdgesData.retained_edge_data e he with
        ⟨_hsrc, _htgt, _hne, i, hseg, k, hk, horient, _hsub, _hcarrier⟩
      rcases horient with hdir | hrev
      · subst e
        exact retainedEdgesData.elementary_no_cut_open i hseg k hk v hv
      · subst e
        simpa [openSegment_symm] using
          (retainedEdgesData.elementary_no_cut_open i hseg k hk v hv)
  have retained_distinct_edges_meet_at_common_endpoints :
      ∀ e f : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2),
        e ∈ retainedEdgesData.retainedEdges →
          f ∈ retainedEdgesData.retainedEdges →
            e ≠ f →
              segment ℝ e.1 e.2 ∩ segment ℝ f.1 f.2 =
                ({e.1, e.2} : Set (EuclideanSpace ℝ (Fin 2))) ∩
                  ({f.1, f.2} : Set (EuclideanSpace ℝ (Fin 2))) :=
    PolygonalPathRetainedElementaryEdgesDistinctMeetAtCommonEndpoints
      γ cutVertices hcut_finite_pair retainedEdgesData
  rcases PolygonalPathRetainedElementaryRawWalkExists
      γ cutVertices hcut_original retainedEdgesData with
    ⟨rawWalk, hraw_head, hraw_last, hraw_len, hraw_mem, hraw_steps⟩
  have hsource_vertex : γ.source ∈ γ.vertices := by
    cases hverts : γ.vertices with
    | nil => exact False.elim (γ.vertices_nonempty hverts)
    | cons x xs =>
        have hx : x = γ.source := by
          simpa [hverts] using γ.source_eq_head
        simp [hx]
  have htarget_vertex : γ.target ∈ γ.vertices := by
    have hlast : γ.vertices.getLast γ.vertices_nonempty = γ.target := by
      simpa [List.getLast?_eq_getLast_of_ne_nil γ.vertices_nonempty] using
        γ.target_eq_last
    rw [← hlast]
    exact List.getLast_mem γ.vertices_nonempty
  refine ⟨
    { vertices := cutVertices
      edges := retainedEdgesData.retainedEdges
      original_vertices_mem := hcut_original
      source_mem := hcut_original γ.source hsource_vertex
      target_mem := hcut_original γ.target htarget_vertex
      edge_source_mem := ?_
      edge_target_mem := ?_
      edge_nondegenerate := ?_
      edge_refines_path_segment := ?_
      edge_subset_carrier := ?_
      no_vertex_in_edge_interior := retained_no_cut_open
      distinct_edges_meet_at_common_endpoints :=
        retained_distinct_edges_meet_at_common_endpoints
      rawWalk := rawWalk
      rawWalk_head := hraw_head
      rawWalk_last := hraw_last
      rawWalk_length_ge_two := hraw_len
      rawWalk_vertices_mem := hraw_mem
      rawWalk_steps := hraw_steps }⟩
  · intro e he
    exact (retainedEdgesData.retained_edge_data e he).1
  · intro e he
    exact (retainedEdgesData.retained_edge_data e he).2.1
  · intro e he
    exact (retainedEdgesData.retained_edge_data e he).2.2.1
  · intro e he
    rcases (retainedEdgesData.retained_edge_data e he).2.2.2 with
      ⟨i, _hseg, _k, _hk, _horient, hsub, _hcarrier⟩
    exact ⟨i.1, by omega, hsub⟩
  · intro e he
    rcases (retainedEdgesData.retained_edge_data e he).2.2.2 with
      ⟨_i, _hseg, _k, _hk, _horient, _hsub, hcarrier⟩
    exact hcarrier
