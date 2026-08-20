import ErdosProblems.Erdos733.ST.PolygonalPath
import ErdosProblems.Erdos733.ST.FinitePolygonalSet

open Classical
noncomputable section

-- [TABLET NODE: PolygonalPathInGeneralPosition]
def PolygonalPathInGeneralPosition (γ : PolygonalPath) (K : FinitePolygonalSet) : Prop :=
-- BODY
  (∀ v : EuclideanSpace ℝ (Fin 2), v ∈ γ.vertices → v ∉ K.carrier) ∧
    (∀ p : EuclideanSpace ℝ (Fin 2), p ∈ K.points → p ∉ γ.carrier) ∧
      (∀ (i : ℕ) (hi : i + 1 < γ.vertices.length)
          (s : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)),
          s ∈ K.segments →
            ¬ ∃ p q : EuclideanSpace ℝ (Fin 2),
              p ≠ q ∧
                segment ℝ p q ⊆
                  segment ℝ γ.vertices[i] γ.vertices[i + 1] ∩ segment ℝ s.1 s.2) ∧
        (∀ (i : ℕ) (hi : i + 1 < γ.vertices.length)
            (s : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2))
            (hs : s ∈ K.segments) (p : EuclideanSpace ℝ (Fin 2)),
            p ∈ openSegment ℝ γ.vertices[i] γ.vertices[i + 1] →
              p ∈ openSegment ℝ s.1 s.2 →
                ¬ ∃ c : ℝ, s.2 - s.1 = c • (γ.vertices[i + 1] - γ.vertices[i])) ∧
          Set.Finite (γ.carrier ∩ K.carrier)
