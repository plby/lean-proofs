import ErdosProblems.Erdos733.ST.PolygonalArc

open Classical
noncomputable section

-- [TABLET NODE: PolygonalArcPointCutData]
structure PolygonalArcPointCutData
    (Q : PolygonalArc) (c : EuclideanSpace ℝ (Fin 2)) where
-- BODY
  prefixArc : PolygonalArc
  suffixArc : PolygonalArc
  cutIndex : ℕ
  cutIndex_valid : cutIndex + 1 < Q.vertices.length
  cut_mem_segment : c ∈ segment ℝ Q.vertices[cutIndex] Q.vertices[cutIndex + 1]
  prefix_vertices_exact :
    prefixArc.vertices = Q.vertices.take (cutIndex + 1) ++ [c]
  suffixDropIndex : ℕ
  suffix_vertices_exact :
    suffixArc.vertices = c :: Q.vertices.drop suffixDropIndex
  suffix_drop_index_spec :
    (suffixDropIndex = cutIndex + 1 ∧ c ≠ Q.vertices[cutIndex + 1]) ∨
      (suffixDropIndex = cutIndex + 2 ∧ c = Q.vertices[cutIndex + 1])
  prefix_source : prefixArc.source = Q.source
  prefix_target : prefixArc.target = c
  suffix_source : suffixArc.source = c
  suffix_target : suffixArc.target = Q.target
  prefix_carrier_subset : prefixArc.carrier ⊆ Q.carrier
  suffix_carrier_subset : suffixArc.carrier ⊆ Q.carrier
  carrier_decomposition : Q.carrier = prefixArc.carrier ∪ suffixArc.carrier
  carrier_intersection : prefixArc.carrier ∩ suffixArc.carrier = {c}
  prefix_carrier_region :
    prefixArc.carrier =
      {z | ∃ i : ℕ, ∃ hi : i + 1 < Q.vertices.length,
        i < cutIndex ∧ z ∈ segment ℝ Q.vertices[i] Q.vertices[i + 1]} ∪
        segment ℝ Q.vertices[cutIndex] c
  suffix_carrier_region :
    suffixArc.carrier =
      segment ℝ c Q.vertices[cutIndex + 1] ∪
        {z | ∃ i : ℕ, ∃ hi : i + 1 < Q.vertices.length,
          cutIndex < i ∧ z ∈ segment ℝ Q.vertices[i] Q.vertices[i + 1]}
  prefix_segment_transfer :
    ∀ z i (hi : i + 1 < Q.vertices.length),
      z ∈ openSegment ℝ Q.vertices[i] Q.vertices[i + 1] →
      z ∈ prefixArc.carrier →
      z ≠ c →
      ∃ j : ℕ, ∃ hj : j + 1 < prefixArc.vertices.length,
        z ∈ openSegment ℝ prefixArc.vertices[j] prefixArc.vertices[j + 1] ∧
          ∃ scale : ℝ, scale ≠ 0 ∧
            prefixArc.vertices[j + 1] - prefixArc.vertices[j] =
              scale • (Q.vertices[i + 1] - Q.vertices[i])
  suffix_segment_transfer :
    ∀ z i (hi : i + 1 < Q.vertices.length),
      z ∈ openSegment ℝ Q.vertices[i] Q.vertices[i + 1] →
      z ∈ suffixArc.carrier →
      z ≠ c →
      ∃ j : ℕ, ∃ hj : j + 1 < suffixArc.vertices.length,
        z ∈ openSegment ℝ suffixArc.vertices[j] suffixArc.vertices[j + 1] ∧
          ∃ scale : ℝ, scale ≠ 0 ∧
            suffixArc.vertices[j + 1] - suffixArc.vertices[j] =
              scale • (Q.vertices[i + 1] - Q.vertices[i])
  protected_first_vertices :
    ∀ (hi : 0 + 1 < Q.vertices.length),
      c ∉ segment ℝ Q.vertices[0] Q.vertices[1] →
      ∃ hprefix : 0 + 1 < prefixArc.vertices.length,
        prefixArc.vertices[0] = Q.vertices[0] ∧
          prefixArc.vertices[1] = Q.vertices[1]
