import Util.IncidenceGeometry.PolygonalPath
import Util.IncidenceGeometry.FinitePolygonalSet

open Classical
noncomputable section

def PolygonalPathIntersectionMultiplicity (γ : PolygonalPath) (K : FinitePolygonalSet) : ℕ :=
  (Finset.range γ.vertices.length).sum fun i =>
    if hi : i + 1 < γ.vertices.length then
      if γ.vertices[i] = γ.vertices[i + 1] then
        0
      else
        K.segments.sum fun s =>
          Set.ncard (openSegment ℝ γ.vertices[i] γ.vertices[i + 1] ∩
            openSegment ℝ s.1 s.2)
    else
      0
