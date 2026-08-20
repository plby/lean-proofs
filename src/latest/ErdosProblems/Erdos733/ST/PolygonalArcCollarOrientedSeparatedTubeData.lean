import ErdosProblems.Erdos733.ST.PolygonalArcCollarSeparatedTubeData

-- [TABLET NODE: PolygonalArcCollarOrientedSeparatedTubeData]
structure PolygonalArcCollarOrientedSeparatedTubeData (γ : PolygonalArc) {η : ℝ}
    (controlRadii : PolygonalArcCollarControlRadii γ η)
    (middleSegments : PolygonalArcCollarMiddleSegmentData γ controlRadii)
    (forbiddenMargins :
      PolygonalArcCollarMiddleForbiddenMargins γ controlRadii middleSegments)
    extends
      PolygonalArcCollarSeparatedTubeData γ controlRadii middleSegments
        forbiddenMargins where
-- BODY
  normal_eq_positive_quarter_turn :
    ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
      normal j hj =
        WithLp.toLp 2 (fun k : Fin 2 =>
          if k = 0 then -((γ.vertices[j + 1] - γ.vertices[j]) 1)
          else (γ.vertices[j + 1] - γ.vertices[j]) 0)
