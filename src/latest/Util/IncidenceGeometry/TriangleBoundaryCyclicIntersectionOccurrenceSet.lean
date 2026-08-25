import Util.IncidenceGeometry.CyclicCurvePresentation

open Classical
noncomputable section

def TriangleBoundaryCyclicIntersectionOccurrenceSet
    {J : SimpleClosedPolygonalCurve} {K : FinitePolygonalSet}
    (R : CyclicCurvePresentation J K)
    (z a b : EuclideanSpace ℝ (Fin 2)) :
    Set ({p : EuclideanSpace ℝ (Fin 2) // p ∈ R.vertices} × Fin 3 ×
      EuclideanSpace ℝ (Fin 2)) :=
  {q | q.2.2 ∈ openSegment ℝ q.1.1 (R.successor q.1).1 ∧
    ((q.2.1 = (0 : Fin 3) ∧ q.2.2 ∈ openSegment ℝ z a) ∨
      (q.2.1 = (1 : Fin 3) ∧ q.2.2 ∈ openSegment ℝ a b) ∨
        (q.2.1 = (2 : Fin 3) ∧ q.2.2 ∈ openSegment ℝ b z))}
