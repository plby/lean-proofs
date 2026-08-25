import Mathlib.Tactic
import Util.IncidenceGeometry.PolygonalArc

open Classical
noncomputable section

def PolygonalArcTerminalEndpointSegmentLength (γ : PolygonalArc) : ℝ :=
  let hprev : γ.vertices.length - 2 < γ.vertices.length := by
    have hlen := γ.length_ge_two
    omega
  dist γ.target (γ.vertices[γ.vertices.length - 2]'hprev)
