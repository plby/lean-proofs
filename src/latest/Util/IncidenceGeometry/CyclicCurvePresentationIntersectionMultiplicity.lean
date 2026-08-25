import Util.IncidenceGeometry.CyclicCurvePresentation
import Util.IncidenceGeometry.PolygonalPath

open Classical
noncomputable section

def CyclicCurvePresentationIntersectionMultiplicity
    (γ : PolygonalPath) {J : SimpleClosedPolygonalCurve} {K : FinitePolygonalSet}
    (R : CyclicCurvePresentation J K) : ℕ :=
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
