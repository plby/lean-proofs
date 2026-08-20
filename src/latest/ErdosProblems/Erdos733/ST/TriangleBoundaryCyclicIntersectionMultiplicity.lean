import ErdosProblems.Erdos733.ST.CyclicCurvePresentation

open Classical
noncomputable section

-- [TABLET NODE: TriangleBoundaryCyclicIntersectionMultiplicity]
def TriangleBoundaryCyclicIntersectionMultiplicity
    {J : SimpleClosedPolygonalCurve} {K : FinitePolygonalSet}
    (R : CyclicCurvePresentation J K)
    (z a b : EuclideanSpace ℝ (Fin 2)) : ℕ :=
-- BODY
  R.vertices.attach.sum fun p =>
    Set.ncard (openSegment ℝ p.1 (R.successor p).1 ∩ openSegment ℝ z a) +
      Set.ncard (openSegment ℝ p.1 (R.successor p).1 ∩ openSegment ℝ a b) +
        Set.ncard (openSegment ℝ p.1 (R.successor p).1 ∩ openSegment ℝ b z)
