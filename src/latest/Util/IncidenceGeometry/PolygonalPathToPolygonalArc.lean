import Util.IncidenceGeometry.FiniteWalkCycleErasure
import Util.IncidenceGeometry.PolygonalArc
import Util.IncidenceGeometry.PolygonalPath
import Util.IncidenceGeometry.PolygonalPathRawStraightLineComplexExists
import Util.IncidenceGeometry.PolygonalPathStraightLineComplexOfRaw
import Util.IncidenceGeometry.PolygonalPathStraightLineComplexToArc

open Classical
noncomputable section

lemma PolygonalPathToPolygonalArc (γ : PolygonalPath) :
    γ.source ≠ γ.target →
      ∃ Γ : PolygonalArc,
        Γ.source = γ.source ∧
          Γ.target = γ.target ∧
            Γ.carrier ⊆ γ.carrier ∧
              ∀ i : ℕ, (hi : i + 1 < Γ.vertices.length) →
                ∃ j : ℕ, ∃ hj : j + 1 < γ.vertices.length,
                  segment ℝ Γ.vertices[i] Γ.vertices[i + 1] ⊆
                    segment ℝ γ.vertices[j] γ.vertices[j + 1] := by
  intro hst
  rcases PolygonalPathRawStraightLineComplexExists γ with ⟨R⟩
  rcases PolygonalPathStraightLineComplexOfRaw γ R hst with ⟨C⟩
  exact PolygonalPathStraightLineComplexToArc γ C
