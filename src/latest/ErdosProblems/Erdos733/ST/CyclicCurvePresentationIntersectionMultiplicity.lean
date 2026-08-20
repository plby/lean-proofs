import ErdosProblems.Erdos733.ST.CyclicCurvePresentation
import ErdosProblems.Erdos733.ST.PolygonalPath

open Classical
noncomputable section

-- [TABLET NODE: CyclicCurvePresentationIntersectionMultiplicity]
def CyclicCurvePresentationIntersectionMultiplicity
    (γ : PolygonalPath) {J : SimpleClosedPolygonalCurve} {K : FinitePolygonalSet}
    (R : CyclicCurvePresentation J K) : ℕ :=
-- BODY
  (Finset.range γ.vertices.length).sum fun i =>
    if hi : i + 1 < γ.vertices.length then
      if γ.vertices[i] = γ.vertices[i + 1] then
        0
      else
        R.vertices.attach.sum fun p =>
          Set.ncard (openSegment ℝ γ.vertices[i] γ.vertices[i + 1] ∩
            openSegment ℝ p.1 (R.successor p).1)
    else
      0
