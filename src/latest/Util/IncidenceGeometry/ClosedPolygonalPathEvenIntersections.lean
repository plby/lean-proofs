import Util.IncidenceGeometry.SimpleClosedPolygonalCurve
import Util.IncidenceGeometry.FinitePolygonalSet
import Util.IncidenceGeometry.PolygonalPathInGeneralPosition
import Util.IncidenceGeometry.PolygonalPathIntersectionMultiplicity
import Util.IncidenceGeometry.CyclicCurvePresentation
import Util.IncidenceGeometry.CyclicCurvePresentationIntersectionMultiplicity
import Util.IncidenceGeometry.CyclicPresentationTriangleGeneralPosition
import Util.IncidenceGeometry.FinitePolygonalSetCyclicCurvePresentation
import Util.IncidenceGeometry.PolygonalPathMultiplicityCyclicPresentation
import Util.IncidenceGeometry.CyclicPresentationClosedPathEvenIntersections
import Util.IncidenceGeometry.TriangleBoundaryCyclicIntersectionMultiplicity
import Util.IncidenceGeometry.TriangleBoundaryEvenIntersections

open Classical
noncomputable section

lemma ClosedPolygonalPathEvenIntersections
    (J : SimpleClosedPolygonalCurve) (Γ : PolygonalPath)
    (K : FinitePolygonalSet)
    (hKJ : K.carrier = J.carrier)
    (hΓ : Γ.source = Γ.target)
    (hgp : PolygonalPathInGeneralPosition Γ K) :
    Even (PolygonalPathIntersectionMultiplicity Γ K) := by
  obtain ⟨R⟩ := FinitePolygonalSetCyclicCurvePresentation J K hKJ
  rw [PolygonalPathMultiplicityCyclicPresentation J Γ K hKJ hgp R]
  exact CyclicPresentationClosedPathEvenIntersections J Γ K hΓ hgp R
