import Util.IncidenceGeometry.GeometricArcDrawing
import Util.IncidenceGeometry.EndpointPairMultiplicitySimpleGraph
import Util.IncidenceGeometry.UnitCircle
import Util.IncidenceGeometry.UnitCircleIncidenceCount
import Util.IncidenceGeometry.UnitCircleIncidenceDoubleCount
import Util.IncidenceGeometry.UnitCircleRetainedIncidenceLowerBound
import Util.IncidenceGeometry.UnitCircleRetainedArcQuotientDrawing
import Util.IncidenceGeometry.UnitCirclesIntersectionsAtMostTwo
import Util.IncidenceGeometry.UnitDistanceCount

open Classical
open scoped BigOperators
open scoped Real
noncomputable section

lemma UnitDistanceArcSelectionDrawing (P : Finset (EuclideanSpace ℝ (Fin 2))) :
    ∃ G : SimpleGraph P, ∃ (_ : Fintype G.edgeSet), ∃ D : GeometricArcDrawing G,
      (IncidenceGeometry.unitDistanceCount P : ℝ) - (P.card : ℝ) ≤ (G.edgeFinset.card : ℝ) ∧
        (D.localPairCount : ℝ) ≤ 2 * (P.card : ℝ) ^ 2 := by
  classical
  have hretained := UnitCircleRetainedIncidenceLowerBound P
  rcases UnitCircleRetainedArcQuotientDrawing P with
    ⟨ι, instF, instD, A, endpoint, hAcard, h_nondiag, h_multiplicity, hdraw⟩
  let : Fintype ι := instF
  let : DecidableEq ι := instD
  rcases EndpointPairMultiplicitySimpleGraph A endpoint h_nondiag h_multiplicity with
    ⟨G, hGfin, hhalf, hEdgeFinset⟩
  let : Fintype G.edgeSet := hGfin
  rcases hdraw G hEdgeFinset with ⟨D, hlocal⟩
  refine ⟨G, hGfin, D, ?_, hlocal⟩
  have htwice :
      2 * ((IncidenceGeometry.unitDistanceCount P : ℝ) - (P.card : ℝ)) ≤ (A.card : ℝ) := by
    rw [hAcard]
    linarith [hretained]
  have htoHalf :
      (IncidenceGeometry.unitDistanceCount P : ℝ) - (P.card : ℝ) ≤ (A.card : ℝ) / 2 := by
    linarith
  exact htoHalf.trans hhalf
