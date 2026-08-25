import Util.IncidenceGeometry.PolygonalArcPointCutData

open Classical
noncomputable section

structure PolygonalArcFirstBallCutData
    (Q : PolygonalArc)
    (p : EuclideanSpace ℝ (Fin 2)) (radius : ℝ) where
  gate : EuclideanSpace ℝ (Fin 2)
  cut : PolygonalArcPointCutData Q gate
  gate_mem_relativeInterior : gate ∈ Q.relativeInterior
  gate_mem_sphere : gate ∈ Metric.sphere p radius
  gate_mem_closure_ball_part :
    gate ∈ closure (Q.carrier ∩ Metric.ball p radius)
  prefix_avoids_ball : Disjoint cut.prefixArc.carrier (Metric.ball p radius)
  ball_part_in_suffix :
    Q.carrier ∩ Metric.ball p radius ⊆ cut.suffixArc.relativeInterior
