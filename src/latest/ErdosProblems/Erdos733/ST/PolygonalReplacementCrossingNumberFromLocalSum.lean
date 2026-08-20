import ErdosProblems.Erdos733.ST.GeometricArcDrawing
import ErdosProblems.Erdos733.ST.CrossingNumber

open Classical
noncomputable section

-- [TABLET NODE: PolygonalReplacementCrossingNumberFromLocalSum]
lemma PolygonalReplacementCrossingNumberFromLocalSum {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet] (D : GeometricArcDrawing G)
    (D' : OrdinaryPolygonalDrawing G)
    (hsum :
      D'.crossingSet.card ≤
        D.intersectionPoints.sum (fun p =>
          Nat.choose (((Finset.univ : Finset G.edgeFinset).filter
            (fun e => p ∈ D.edgeRelativeInterior e)).card) 2)) :
    D'.crossingSet.card ≤ D.localPairCount ∧
      CrossingNumber G ≤ D.localPairCount := by
-- BODY
  have hcard : D'.crossingSet.card ≤ D.localPairCount := by
    simpa [D.localPairCount_eq] using hsum
  refine ⟨hcard, ?_⟩
  rw [CrossingNumber]
  exact (Nat.sInf_le
    (show D'.crossingSet.card ∈
        Set.range (fun E : OrdinaryPolygonalDrawing G => E.crossingSet.card) from
      ⟨D', rfl⟩)).trans hcard
