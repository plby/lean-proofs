import Mathlib.Tactic
import Util.IncidenceGeometry.PolygonalArc
import Util.IncidenceGeometry.PolygonalArcInitialEndpointSegmentLength
import Util.IncidenceGeometry.PolygonalArcTerminalEndpointSegmentLength

open Classical
noncomputable section

structure PolygonalArcEndpointIsolation (γ : PolygonalArc) (r₀ r₁ : ℝ) : Prop where
  source_pos : 0 < r₀
  target_pos : 0 < r₁
  source_lt_initial_length : r₀ < PolygonalArcInitialEndpointSegmentLength γ
  target_lt_terminal_length : r₁ < PolygonalArcTerminalEndpointSegmentLength γ
  endpoint_closedBalls_disjoint :
    Disjoint (Metric.closedBall γ.source r₀) (Metric.closedBall γ.target r₁)
  source_closedBall_carrier_subset_initial_segment :
    let hfirst : 1 < γ.vertices.length := Nat.lt_of_succ_le γ.length_ge_two
    Metric.closedBall γ.source r₀ ∩ γ.carrier ⊆
      segment ℝ γ.source (γ.vertices[1]'hfirst)
  target_closedBall_carrier_subset_terminal_segment :
    let hprev : γ.vertices.length - 2 < γ.vertices.length := by
      have hlen := γ.length_ge_two
      omega
    Metric.closedBall γ.target r₁ ∩ γ.carrier ⊆
      segment ℝ γ.target (γ.vertices[γ.vertices.length - 2]'hprev)
