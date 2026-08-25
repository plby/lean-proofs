import Util.IncidenceGeometry.PolygonalArc

open Classical
noncomputable section

structure PolygonalArcOrderedBallCutData
    (Q : PolygonalArc)
    (p : EuclideanSpace ℝ (Fin 2)) (radius : ℝ) where
  qminus : EuclideanSpace ℝ (Fin 2)
  qplus : EuclideanSpace ℝ (Fin 2)
  prefixArc : PolygonalArc
  middleArc : PolygonalArc
  suffixArc : PolygonalArc
  qminus_ne_qplus : qminus ≠ qplus
  qminus_mem_relativeInterior : qminus ∈ Q.relativeInterior
  qplus_mem_relativeInterior : qplus ∈ Q.relativeInterior
  qminus_mem_sphere : qminus ∈ Metric.sphere p radius
  qplus_mem_sphere : qplus ∈ Metric.sphere p radius
  qminus_mem_closure_ball_part :
    qminus ∈ closure (Q.carrier ∩ Metric.ball p radius)
  qplus_mem_closure_ball_part :
    qplus ∈ closure (Q.carrier ∩ Metric.ball p radius)
  source_not_mem_closedBall : Q.source ∉ Metric.closedBall p radius
  target_not_mem_closedBall : Q.target ∉ Metric.closedBall p radius
  prefix_source : prefixArc.source = Q.source
  prefix_target : prefixArc.target = qminus
  middle_source : middleArc.source = qminus
  middle_target : middleArc.target = qplus
  suffix_source : suffixArc.source = qplus
  suffix_target : suffixArc.target = Q.target
  prefix_carrier_subset : prefixArc.carrier ⊆ Q.carrier
  middle_carrier_subset : middleArc.carrier ⊆ Q.carrier
  suffix_carrier_subset : suffixArc.carrier ⊆ Q.carrier
  carrier_decomposition :
    Q.carrier = prefixArc.carrier ∪ middleArc.carrier ∪ suffixArc.carrier
  prefix_middle_intersection :
    prefixArc.carrier ∩ middleArc.carrier = {qminus}
  middle_suffix_intersection :
    middleArc.carrier ∩ suffixArc.carrier = {qplus}
  prefix_suffix_disjoint : Disjoint prefixArc.carrier suffixArc.carrier
  prefix_avoids_ball : Disjoint prefixArc.carrier (Metric.ball p radius)
  suffix_avoids_ball : Disjoint suffixArc.carrier (Metric.ball p radius)
  ball_part_in_middle :
    Q.carrier ∩ Metric.ball p radius ⊆ middleArc.relativeInterior
  middle_meets_ball :
    (middleArc.relativeInterior ∩ Metric.ball p radius).Nonempty
  prefix_segment_transfer :
    ∀ z i (hi : i + 1 < Q.vertices.length),
      z ∈ openSegment ℝ Q.vertices[i] Q.vertices[i + 1] →
      z ∈ prefixArc.carrier →
      z ∉ Metric.closedBall p radius →
      ∃ j : ℕ, ∃ hj : j + 1 < prefixArc.vertices.length,
        z ∈ openSegment ℝ prefixArc.vertices[j] prefixArc.vertices[j + 1] ∧
          ∃ c : ℝ, c ≠ 0 ∧
            prefixArc.vertices[j + 1] - prefixArc.vertices[j] =
              c • (Q.vertices[i + 1] - Q.vertices[i])
  suffix_segment_transfer :
    ∀ z i (hi : i + 1 < Q.vertices.length),
      z ∈ openSegment ℝ Q.vertices[i] Q.vertices[i + 1] →
      z ∈ suffixArc.carrier →
      z ∉ Metric.closedBall p radius →
      ∃ j : ℕ, ∃ hj : j + 1 < suffixArc.vertices.length,
        z ∈ openSegment ℝ suffixArc.vertices[j] suffixArc.vertices[j + 1] ∧
          ∃ c : ℝ, c ≠ 0 ∧
            suffixArc.vertices[j + 1] - suffixArc.vertices[j] =
              c • (Q.vertices[i + 1] - Q.vertices[i])
  protected_first_vertices :
    ∀ (hi : 0 + 1 < Q.vertices.length),
      Disjoint
          (segment ℝ Q.vertices[0] Q.vertices[1])
          (Metric.closedBall p radius) →
      ∃ hprefix : 0 + 1 < prefixArc.vertices.length,
        prefixArc.vertices[0] = Q.vertices[0] ∧
          prefixArc.vertices[1] = Q.vertices[1]
