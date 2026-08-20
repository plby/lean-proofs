import Mathlib.Tactic
import ErdosProblems.Erdos733.ST.PolygonalArcCappedCollarAssemblyExists
import ErdosProblems.Erdos733.ST.PolygonalArcCompactAvoidanceScale
import ErdosProblems.Erdos733.ST.PolygonalArcEndpointIsolation
import ErdosProblems.Erdos733.ST.PolygonalArcInitialEndpointCone
import ErdosProblems.Erdos733.ST.PolygonalArcInitialEndpointSegmentLength
import ErdosProblems.Erdos733.ST.PolygonalArcTerminalEndpointCone
import ErdosProblems.Erdos733.ST.PolygonalArcTerminalEndpointSegmentLength

open Classical
noncomputable section

-- [TABLET NODE: PolygonalArcSideStripsAvoidCompactWithEndpointConeCaps]
lemma PolygonalArcSideStripsAvoidCompactWithEndpointConeCaps (γ : PolygonalArc)
    (F A : Set (EuclideanSpace ℝ (Fin 2))) (r₀ r₁ K₀ K₁ : ℝ) :
    IsCompact F →
      Disjoint F γ.carrier →
        IsCompact A →
          Disjoint A γ.carrier →
            PolygonalArcEndpointIsolation γ r₀ r₁ →
              0 < K₀ →
                0 < K₁ →
                    ∃ S : PolygonalSideStrips γ,
                      Disjoint S.collar F ∧
                        Disjoint S.collar A ∧
                          γ.source ∉ S.collar ∧
                            γ.target ∉ S.collar ∧
                              ((S.collar ∩ Metric.ball γ.source r₀) \
                                  γ.relativeInterior ⊆
                                PolygonalArcInitialEndpointCone γ r₀ K₀) ∧
                                ((S.collar ∩ Metric.ball γ.target r₁) \
                                    γ.relativeInterior ⊆
                                  PolygonalArcTerminalEndpointCone γ r₁ K₁) := by
-- BODY
  intro hF hFγ hA hAγ hIso hK₀ hK₁
  have hFAcompact : IsCompact (F ∪ A) := hF.union hA
  have hFAγ : Disjoint (F ∪ A) γ.carrier := by
    rw [Set.disjoint_left]
    intro z hzFA hzγ
    rcases hzFA with hzF | hzA
    · exact (Set.disjoint_left.mp hFγ hzF) hzγ
    · exact (Set.disjoint_left.mp hAγ hzA) hzγ
  obtain ⟨η, hηpos, hηavoid⟩ :=
    PolygonalArcCompactAvoidanceScale γ (F ∪ A) hFAcompact hFAγ
  obtain ⟨S, hsource, htarget, hinit, hterm, hnear⟩ :=
    PolygonalArcCappedCollarAssemblyExists γ η r₀ r₁ K₀ K₁ hηpos
      hIso hK₀ hK₁
  have hSF : Disjoint S.collar F := by
    rw [Set.disjoint_left]
    intro z hzS hzF
    exact hηavoid z (hnear z hzS) (Or.inl hzF)
  have hSA : Disjoint S.collar A := by
    rw [Set.disjoint_left]
    intro z hzS hzA
    exact hηavoid z (hnear z hzS) (Or.inr hzA)
  exact ⟨S, hSF, hSA, hsource, htarget, hinit, hterm⟩
