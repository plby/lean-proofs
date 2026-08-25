import Util.IncidenceGeometry.IsAffineLine
import Util.IncidenceGeometry.LineIncidences
import Util.IncidenceGeometry.GeometricArcDrawing
import Util.IncidenceGeometry.PointLineConsecutivePairGraphDataExists
import Util.IncidenceGeometry.PointLineConsecutivePairStraightDrawing

open Classical
noncomputable section

lemma PointLineConsecutivePairDrawing
    (P : Finset (EuclideanSpace ℝ (Fin 2)))
    (L : Finset {ℓ : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2)) // IsAffineLine ℓ}) :
    ∃ (G : SimpleGraph P), ∃ (_ : Fintype G.edgeSet),
      ∃ D : GeometricArcDrawing G, ∃ ell : ℕ,
        ell ≤ L.card ∧
          LineIncidences P L = G.edgeFinset.card + ell ∧
            D.localPairCount ≤ ell ^ 2 := by
  obtain ⟨A⟩ := PointLineConsecutivePairGraphDataExists P L
  obtain ⟨D, hD⟩ := PointLineConsecutivePairStraightDrawing A
  exact ⟨A.graph, inferInstance, D, A.retainedLines.card,
    Finset.card_le_card A.retainedLines_subset, A.incidence_eq, hD⟩
