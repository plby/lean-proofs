import Util.IncidenceGeometry.PolygonalArcCollarMiddleSegmentData

structure PolygonalArcCollarMiddleForbiddenMargins (γ : PolygonalArc) {η : ℝ}
    (controlRadii : PolygonalArcCollarControlRadii γ η)
    (middleSegments : PolygonalArcCollarMiddleSegmentData γ controlRadii) where
  margin : (j : ℕ) → j + 1 < γ.vertices.length → ℝ
  margin_pos :
    ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length), 0 < margin j hj
  middle_segment_separation :
    ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length)
      (k : ℕ) (hk : k + 1 < γ.vertices.length),
        (j + 1 < k ∨ k + 1 < j) →
          ∀ z, z ∈ middleSegments.middle j hj →
            ∀ q, q ∈ segment ℝ γ.vertices[k] γ.vertices[k + 1] →
              margin j hj ≤ dist z q
  middle_control_disk_separation :
    ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length)
      (i : Fin γ.vertices.length),
        i.1 ≠ j → i.1 ≠ j + 1 →
          ∀ z, z ∈ middleSegments.middle j hj →
            ∀ q, q ∈ Metric.closedBall γ.vertices[i.1] (controlRadii.radius i) →
              margin j hj ≤ dist z q
  middle_core_separation :
    ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length)
      (k : ℕ) (hk : k + 1 < γ.vertices.length),
        (j + 1 < k ∨ k + 1 < j) →
          ∀ z, z ∈ middleSegments.middle j hj →
            ∀ q, q ∈ middleSegments.middle k hk →
              margin j hj ≤ dist z q
