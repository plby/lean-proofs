import ErdosProblems.Erdos733.ST.IsAffineLine
import ErdosProblems.Erdos733.ST.LineIncidences
import ErdosProblems.Erdos733.ST.GeometricArcDrawing
import ErdosProblems.Erdos733.ST.PointLineConsecutivePairGraphDataExists
import ErdosProblems.Erdos733.ST.PointLineConsecutivePairStraightDrawing

open Classical
noncomputable section

-- [TABLET NODE: PointLineConsecutivePairDrawing]
lemma PointLineConsecutivePairDrawing
    (P : Finset (EuclideanSpace ℝ (Fin 2)))
    (L : Finset {ℓ : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2)) // IsAffineLine ℓ}) :
    ∃ (G : SimpleGraph P), ∃ (_ : Fintype G.edgeSet),
      ∃ D : GeometricArcDrawing G, ∃ ell : ℕ,
        ell ≤ L.card ∧
          LineIncidences P L = G.edgeFinset.card + ell ∧
            D.localPairCount ≤ ell ^ 2 := by
-- BODY
  obtain ⟨A⟩ := PointLineConsecutivePairGraphDataExists P L
  obtain ⟨D, hD⟩ := PointLineConsecutivePairStraightDrawing A
  exact ⟨A.graph, inferInstance, D, A.retainedLines.card,
    Finset.card_le_card A.retainedLines_subset, A.incidence_eq, hD⟩
