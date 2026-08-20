import ErdosProblems.Erdos733.ST.SimpleClosedPolygonalCurve
import ErdosProblems.Erdos733.ST.FinitePolygonalSet
import ErdosProblems.Erdos733.ST.PolygonalPathInGeneralPosition
import ErdosProblems.Erdos733.ST.PolygonalPathIntersectionMultiplicity
import ErdosProblems.Erdos733.ST.CyclicCurvePresentation
import ErdosProblems.Erdos733.ST.CyclicCurvePresentationIntersectionMultiplicity
import ErdosProblems.Erdos733.ST.CyclicPresentationTriangleGeneralPosition
import ErdosProblems.Erdos733.ST.FinitePolygonalSetCyclicCurvePresentation
import ErdosProblems.Erdos733.ST.PolygonalPathMultiplicityCyclicPresentation
import ErdosProblems.Erdos733.ST.CyclicPresentationClosedPathEvenIntersections
import ErdosProblems.Erdos733.ST.TriangleBoundaryCyclicIntersectionMultiplicity
import ErdosProblems.Erdos733.ST.TriangleBoundaryEvenIntersections

open Classical
noncomputable section

-- [TABLET NODE: ClosedPolygonalPathEvenIntersections]
lemma ClosedPolygonalPathEvenIntersections
    (J : SimpleClosedPolygonalCurve) (Γ : PolygonalPath)
    (K : FinitePolygonalSet)
    (hKJ : K.carrier = J.carrier)
    (hΓ : Γ.source = Γ.target)
    (hgp : PolygonalPathInGeneralPosition Γ K) :
    Even (PolygonalPathIntersectionMultiplicity Γ K) := by
-- BODY
  obtain ⟨R⟩ := FinitePolygonalSetCyclicCurvePresentation J K hKJ
  rw [PolygonalPathMultiplicityCyclicPresentation J Γ K hKJ hgp R]
  exact CyclicPresentationClosedPathEvenIntersections J Γ K hΓ hgp R
