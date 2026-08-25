import Util.IncidenceGeometry.PolygonalArc

open Classical
noncomputable section

def PolygonalArcInitialEndpointSegmentLength (γ : PolygonalArc) : ℝ :=
  let hfirst : 1 < γ.vertices.length := Nat.lt_of_succ_le γ.length_ge_two
  dist γ.source (γ.vertices[1]'hfirst)
