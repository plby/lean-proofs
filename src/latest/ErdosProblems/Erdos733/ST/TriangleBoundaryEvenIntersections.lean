import ErdosProblems.Erdos733.ST.CyclicCurvePresentation
import ErdosProblems.Erdos733.ST.CyclicPresentationTriangleGeneralPosition
import ErdosProblems.Erdos733.ST.TriangleBoundaryCyclicIntersectionMultiplicity
import ErdosProblems.Erdos733.ST.TriangleBoundaryMultiplicityEqualsOccurrenceNcard
import ErdosProblems.Erdos733.ST.TriangleBoundaryOccurrenceSetEvenByIntervals

open Classical
noncomputable section

-- [TABLET NODE: TriangleBoundaryEvenIntersections]
lemma TriangleBoundaryEvenIntersections
    {J : SimpleClosedPolygonalCurve} {K : FinitePolygonalSet}
    (R : CyclicCurvePresentation J K)
    (z a b : EuclideanSpace ℝ (Fin 2))
    (hza : z ≠ a) (hab : a ≠ b) (hbz : b ≠ z)
    (hncol : ¬ ∃ c : ℝ, b - a = c • (z - a))
    (hgp : CyclicPresentationTriangleGeneralPosition R z a b) :
    Even (TriangleBoundaryCyclicIntersectionMultiplicity R z a b) := by
-- BODY
  rw [TriangleBoundaryMultiplicityEqualsOccurrenceNcard R z a b hgp]
  exact TriangleBoundaryOccurrenceSetEvenByIntervals R z a b hza hab hbz hncol hgp
