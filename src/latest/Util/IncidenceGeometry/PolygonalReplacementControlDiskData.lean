import Util.IncidenceGeometry.GeometricArcDrawing

open Classical
noncomputable section

structure PolygonalReplacementControlDiskData {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet] (D : GeometricArcDrawing G) where
  vertexRadius : V → ℝ
  vertexRadius_pos : ∀ v, 0 < vertexRadius v
  intersectionRadius : {p // p ∈ D.intersectionPoints} → ℝ
  intersectionRadius_pos : ∀ x, 0 < intersectionRadius x
  vertex_vertex_disjoint :
    ∀ ⦃v w⦄, v ≠ w →
      Disjoint (Metric.closedBall (D.vertexPlacement v) (vertexRadius v))
        (Metric.closedBall (D.vertexPlacement w) (vertexRadius w))
  vertex_intersection_disjoint :
    ∀ v x,
      Disjoint (Metric.closedBall (D.vertexPlacement v) (vertexRadius v))
        (Metric.closedBall x.1 (intersectionRadius x))
  intersection_intersection_disjoint :
    ∀ ⦃x y⦄, x ≠ y →
      Disjoint (Metric.closedBall x.1 (intersectionRadius x))
        (Metric.closedBall y.1 (intersectionRadius y))
  vertex_disk_meets_only_incident_edges :
    ∀ ⦃v e p⦄,
      p ∈ Metric.closedBall (D.vertexPlacement v) (vertexRadius v) →
        p ∈ D.edgeCarrier e → v ∈ e.1
  vertex_boundary_unique :
    ∀ ⦃v e⦄, v ∈ e.1 →
      ∃! p : EuclideanSpace ℝ (Fin 2),
        p ∈ Metric.sphere (D.vertexPlacement v) (vertexRadius v) ∧
          p ∈ D.edgeCarrier e
  vertex_boundary_point_edge_unique :
    ∀ ⦃v e₁ e₂ p⦄,
      v ∈ e₁.1 →
        v ∈ e₂.1 →
          p ∈ Metric.sphere (D.vertexPlacement v) (vertexRadius v) →
            p ∈ D.edgeCarrier e₁ →
              p ∈ D.edgeCarrier e₂ → e₁ = e₂
  intersection_disk_meets_only_passing_edges :
    ∀ ⦃x : {p // p ∈ D.intersectionPoints}⦄ ⦃e p⦄,
      p ∈ Metric.closedBall x.1 (intersectionRadius x) →
        p ∈ D.edgeCarrier e → x.1 ∈ D.edgeRelativeInterior e
  intersection_boundary_two_points :
    ∀ ⦃x : {p // p ∈ D.intersectionPoints}⦄ ⦃e⦄,
      x.1 ∈ D.edgeRelativeInterior e →
        ∃ a b : EuclideanSpace ℝ (Fin 2),
          a ≠ b ∧
            a ∈ Metric.sphere x.1 (intersectionRadius x) ∧
              a ∈ D.edgeCarrier e ∧
                b ∈ Metric.sphere x.1 (intersectionRadius x) ∧
                  b ∈ D.edgeCarrier e ∧
                    ∀ p,
                      p ∈ Metric.sphere x.1 (intersectionRadius x) →
                        p ∈ D.edgeCarrier e → p = a ∨ p = b
  intersection_boundary_point_edge_unique :
    ∀ ⦃x : {p // p ∈ D.intersectionPoints}⦄ ⦃e₁ e₂ p⦄,
      x.1 ∈ D.edgeRelativeInterior e₁ →
        x.1 ∈ D.edgeRelativeInterior e₂ →
          p ∈ Metric.sphere x.1 (intersectionRadius x) →
            p ∈ D.edgeCarrier e₁ →
              p ∈ D.edgeCarrier e₂ → e₁ = e₂
