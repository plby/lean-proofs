import ErdosProblems.Erdos733.ST.PolygonalArc

open Classical
noncomputable section

-- [TABLET NODE: PolygonalArcInitialEndpointSegmentLength]
def PolygonalArcInitialEndpointSegmentLength (γ : PolygonalArc) : ℝ :=
-- BODY
  let hfirst : 1 < γ.vertices.length := Nat.lt_of_succ_le γ.length_ge_two
  dist γ.source (γ.vertices[1]'hfirst)
