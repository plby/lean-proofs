import Util.IncidenceGeometry.CrossingNumber
import Util.IncidenceGeometry.PolygonalReplacementForGeometricArcs
import Util.IncidenceGeometry.UnitCircle
import Util.IncidenceGeometry.UnitCircleIncidenceCount
import Util.IncidenceGeometry.UnitCircleIncidenceDoubleCount
import Util.IncidenceGeometry.UnitCirclesIntersectionsAtMostTwo
import Util.IncidenceGeometry.UnitDistanceArcSelectionDrawing
import Util.IncidenceGeometry.UnitDistanceCount

open Classical
open scoped Real
noncomputable section

lemma UnitDistanceArcGraph (P : Finset (EuclideanSpace ℝ (Fin 2))) :
    ∃ G : SimpleGraph P, ∃ (_ : Fintype G.edgeSet),
      (IncidenceGeometry.unitDistanceCount P : ℝ) - (P.card : ℝ) ≤ (G.edgeFinset.card : ℝ) ∧
        (CrossingNumber G : ℝ) ≤ 2 * (P.card : ℝ) ^ 2 := by
  rcases UnitDistanceArcSelectionDrawing P with ⟨G, hGfin, D, hedge, hlocal⟩
  let := hGfin
  rcases PolygonalReplacementForGeometricArcs G D with ⟨_D', _hcard, hcross⟩
  refine ⟨G, hGfin, hedge, ?_⟩
  exact (Nat.cast_le.mpr hcross).trans hlocal
