import Mathlib.Tactic
import ErdosProblems.Erdos733.ST.PolygonalArcCollarCompatibleOrientedTubeDataEndpointRefinement
import ErdosProblems.Erdos733.ST.PolygonalArcCollarCompatibleOrientedTubeDataExists

open Classical
noncomputable section

-- [TABLET NODE: PolygonalArcCollarCompatibleOrientedTubeDataExistsBelow]
lemma PolygonalArcCollarCompatibleOrientedTubeDataExistsBelow (γ : PolygonalArc)
    {η : ℝ} (controlRadii : PolygonalArcCollarControlRadii γ η)
    (middleSegments : PolygonalArcCollarMiddleSegmentData γ controlRadii)
    (forbiddenMargins :
      PolygonalArcCollarMiddleForbiddenMargins γ controlRadii middleSegments)
    (r₀ r₁ K₀ K₁ : ℝ) :
    PolygonalArcEndpointIsolation γ r₀ r₁ →
      0 < K₀ →
      0 < K₁ →
        let hfirst : 0 + 1 < γ.vertices.length := by
          have hlen := γ.length_ge_two
          omega
        let jlast : ℕ := γ.vertices.length - 2
        let hlast : jlast + 1 < γ.vertices.length := by
          have hlen := γ.length_ge_two
          dsimp [jlast]
          omega
        ∃ compatibleTubes :
          PolygonalArcCollarCompatibleOrientedTubeData γ controlRadii
            middleSegments forbiddenMargins,
          compatibleTubes.initialConeBound 0 hfirst < K₀ ∧
            compatibleTubes.terminalConeBound jlast hlast < K₁ ∧
              (∀ (j : ℕ) (hj : j + 1 < γ.vertices.length), j ≠ 0 →
                Disjoint
                  (compatibleTubes.orientedTubes.toPolygonalArcCollarSeparatedTubeData.tube
                    j hj)
                  (Metric.ball γ.source r₀)) ∧
                (∀ (j : ℕ) (hj : j + 1 < γ.vertices.length), j ≠ jlast →
                  Disjoint
                    (compatibleTubes.orientedTubes.toPolygonalArcCollarSeparatedTubeData.tube
                      j hj)
                    (Metric.ball γ.target r₁)) := by
-- BODY
  intro hIso hK₀ hK₁
  obtain ⟨base⟩ :=
    PolygonalArcCollarCompatibleOrientedTubeDataExists γ controlRadii middleSegments
      forbiddenMargins
  exact
    PolygonalArcCollarCompatibleOrientedTubeDataEndpointRefinement
      (γ := γ) (controlRadii := controlRadii) (middleSegments := middleSegments)
      (forbiddenMargins := forbiddenMargins) (base := base)
      (r₀ := r₀) (r₁ := r₁) (K₀ := K₀) (K₁ := K₁)
      hIso hK₀ hK₁
