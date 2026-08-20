import Mathlib.Tactic
import ErdosProblems.Erdos733.ST.PolygonalArc

open Classical
noncomputable section

-- [TABLET NODE: PolygonalArcTerminalEndpointSegmentLength]
def PolygonalArcTerminalEndpointSegmentLength (γ : PolygonalArc) : ℝ :=
-- BODY
  let hprev : γ.vertices.length - 2 < γ.vertices.length := by
    have hlen := γ.length_ge_two
    omega
  dist γ.target (γ.vertices[γ.vertices.length - 2]'hprev)
