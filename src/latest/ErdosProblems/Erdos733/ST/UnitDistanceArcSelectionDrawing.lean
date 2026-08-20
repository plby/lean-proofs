import ErdosProblems.Erdos733.ST.GeometricArcDrawing
import ErdosProblems.Erdos733.ST.EndpointPairMultiplicitySimpleGraph
import ErdosProblems.Erdos733.ST.UnitCircle
import ErdosProblems.Erdos733.ST.UnitCircleIncidenceCount
import ErdosProblems.Erdos733.ST.UnitCircleIncidenceDoubleCount
import ErdosProblems.Erdos733.ST.UnitCircleRetainedIncidenceLowerBound
import ErdosProblems.Erdos733.ST.UnitCircleRetainedArcQuotientDrawing
import ErdosProblems.Erdos733.ST.UnitCirclesIntersectionsAtMostTwo
import ErdosProblems.Erdos733.ST.unitDist

open Classical
open scoped BigOperators
open scoped Real
noncomputable section

-- [TABLET NODE: UnitDistanceArcSelectionDrawing]
lemma UnitDistanceArcSelectionDrawing (P : Finset (EuclideanSpace ℝ (Fin 2))) :
    ∃ G : SimpleGraph P, ∃ (_ : Fintype G.edgeSet), ∃ D : GeometricArcDrawing G,
      (unitDist P : ℝ) - (P.card : ℝ) ≤ (G.edgeFinset.card : ℝ) ∧
        (D.localPairCount : ℝ) ≤ 2 * (P.card : ℝ) ^ 2 := by
-- BODY
  classical
  have hretained := UnitCircleRetainedIncidenceLowerBound P
  rcases UnitCircleRetainedArcQuotientDrawing P with
    ⟨ι, instF, instD, A, endpoint, hAcard, h_nondiag, h_multiplicity, hdraw⟩
  letI : Fintype ι := instF
  letI : DecidableEq ι := instD
  rcases EndpointPairMultiplicitySimpleGraph A endpoint h_nondiag h_multiplicity with
    ⟨G, hGfin, hhalf, hEdgeFinset⟩
  letI : Fintype G.edgeSet := hGfin
  rcases hdraw G hEdgeFinset with ⟨D, hlocal⟩
  refine ⟨G, hGfin, D, ?_, hlocal⟩
  have htwice :
      2 * ((unitDist P : ℝ) - (P.card : ℝ)) ≤ (A.card : ℝ) := by
    rw [hAcard]
    linarith [hretained]
  have htoHalf :
      (unitDist P : ℝ) - (P.card : ℝ) ≤ (A.card : ℝ) / 2 := by
    linarith
  exact htoHalf.trans hhalf
