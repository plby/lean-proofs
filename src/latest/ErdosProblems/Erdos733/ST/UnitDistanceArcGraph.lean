import ErdosProblems.Erdos733.ST.CrossingNumber
import ErdosProblems.Erdos733.ST.PolygonalReplacementForGeometricArcs
import ErdosProblems.Erdos733.ST.UnitCircle
import ErdosProblems.Erdos733.ST.UnitCircleIncidenceCount
import ErdosProblems.Erdos733.ST.UnitCircleIncidenceDoubleCount
import ErdosProblems.Erdos733.ST.UnitCirclesIntersectionsAtMostTwo
import ErdosProblems.Erdos733.ST.UnitDistanceArcSelectionDrawing
import ErdosProblems.Erdos733.ST.unitDist

open Classical
open scoped Real
noncomputable section

-- [TABLET NODE: UnitDistanceArcGraph]
lemma UnitDistanceArcGraph (P : Finset (EuclideanSpace ℝ (Fin 2))) :
    ∃ G : SimpleGraph P, ∃ (_ : Fintype G.edgeSet),
      (unitDist P : ℝ) - (P.card : ℝ) ≤ (G.edgeFinset.card : ℝ) ∧
        (CrossingNumber G : ℝ) ≤ 2 * (P.card : ℝ) ^ 2 := by
-- BODY
  rcases UnitDistanceArcSelectionDrawing P with ⟨G, hGfin, D, hedge, hlocal⟩
  letI := hGfin
  rcases PolygonalReplacementForGeometricArcs G D with ⟨_D', _hcard, hcross⟩
  refine ⟨G, hGfin, hedge, ?_⟩
  exact (Nat.cast_le.mpr hcross).trans hlocal
