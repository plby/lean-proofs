import ErdosProblems.Erdos733.ST.PolygonalArc

open Classical
noncomputable section

-- [TABLET NODE: OrdinaryCrossingLocalBranchData]
structure OrdinaryCrossingLocalBranchData
    (gamma : PolygonalArc) (p : EuclideanSpace ℝ (Fin 2)) (radius : ℝ) where
-- BODY
  radius_pos : 0 < radius
  beforeIndex : ℕ
  afterIndex : ℕ
  beforeIndex_valid : beforeIndex + 1 < gamma.vertices.length
  afterIndex_valid : afterIndex + 1 < gamma.vertices.length
  center_case :
    (afterIndex = beforeIndex ∧
        p ∈ openSegment ℝ gamma.vertices[beforeIndex]
          gamma.vertices[beforeIndex + 1]) ∨
      (afterIndex = beforeIndex + 1 ∧ p = gamma.vertices[afterIndex])
  beforeGate : EuclideanSpace ℝ (Fin 2)
  afterGate : EuclideanSpace ℝ (Fin 2)
  beforeGate_open :
    beforeGate ∈ openSegment ℝ gamma.vertices[beforeIndex] p
  afterGate_open :
    afterGate ∈ openSegment ℝ p gamma.vertices[afterIndex + 1]
  beforeGate_on_sphere : beforeGate ∈ Metric.sphere p radius
  afterGate_on_sphere : afterGate ∈ Metric.sphere p radius
  gates_ne : beforeGate ≠ afterGate
  closedBall_carrier_eq :
    Metric.closedBall p radius ∩ gamma.carrier =
      Metric.closedBall p radius ∩
        (segment ℝ gamma.vertices[beforeIndex] gamma.vertices[beforeIndex + 1] ∪
          segment ℝ gamma.vertices[afterIndex] gamma.vertices[afterIndex + 1])
  sphere_carrier_eq :
    Metric.sphere p radius ∩ gamma.carrier = {beforeGate, afterGate}
