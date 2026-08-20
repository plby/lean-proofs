import ErdosProblems.Erdos733.ST.PolygonalReplacementControlDiskData

open Classical
noncomputable section

-- [TABLET NODE: PolygonalReplacementOutsideControlDisksDistinctEdgesDisjoint]
lemma PolygonalReplacementOutsideControlDisksDistinctEdgesDisjoint {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet] (D : GeometricArcDrawing G)
    (controlDisks : PolygonalReplacementControlDiskData G D) :
    ∀ ⦃e₁ e₂ : G.edgeFinset⦄ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
      e₁ ≠ e₂ →
        p ∈ D.edgeCarrier e₁ →
          p ∈ D.edgeCarrier e₂ →
            (∀ v : V,
              p ∉ Metric.ball (D.vertexPlacement v) (controlDisks.vertexRadius v)) →
              (∀ x : {q // q ∈ D.intersectionPoints},
                p ∉ Metric.ball x.1 (controlDisks.intersectionRadius x)) →
                False := by
-- BODY
  classical
  have carrier_endpoint_or_interior :
      ∀ (e : G.edgeFinset) {p : EuclideanSpace ℝ (Fin 2)},
        p ∈ D.edgeCarrier e →
          p = D.edgeSource e ∨ p = D.edgeTarget e ∨ p ∈ D.edgeRelativeInterior e := by
    intro e p hp
    rcases D.edge_is_simple_lineSegment_or_circularArc e with hline | harc
    · rcases hline with ⟨_hne, hcarrier, hrel⟩
      by_cases hs : p = D.edgeSource e
      · exact Or.inl hs
      · by_cases ht : p = D.edgeTarget e
        · exact Or.inr (Or.inl ht)
        · exact Or.inr (Or.inr (by
            rw [hrel]
            exact mem_openSegment_of_ne_left_right (𝕜 := ℝ)
              (by simpa [eq_comm] using hs)
              (by simpa [eq_comm] using ht)
              (by simpa [hcarrier] using hp)))
    · rcases harc with ⟨_c, _r, γ, _hr, _hγcont, _hγinj, _hcircle, hsource,
        htarget, hcarrier, hrel⟩
      rw [hcarrier] at hp
      rcases hp with ⟨t, rfl⟩
      by_cases ht0 : t.1 = 0
      · left
        have ht_eq : t = ⟨0, by simp⟩ := Subtype.ext ht0
        simpa [ht_eq, hsource]
      · by_cases ht1 : t.1 = 1
        · right
          left
          have ht_eq : t = ⟨1, by simp⟩ := Subtype.ext ht1
          simpa [ht_eq, htarget]
        · right
          right
          rw [hrel]
          have ht_pos : 0 < t.1 := lt_of_le_of_ne t.2.1 (Ne.symm ht0)
          have ht_lt : t.1 < 1 := lt_of_le_of_ne t.2.2 ht1
          refine ⟨⟨t.1, ht_pos, ht_lt⟩, ?_⟩
          congr
  have edgeSource_vertex :
      ∀ e : G.edgeFinset, ∃ v : V, v ∈ e.1 ∧ D.edgeSource e = D.vertexPlacement v := by
    intro e
    rcases D.edgeArc_endpoints e with ⟨a, b, _hadj, heq, hend⟩
    rcases hend with hend | hend
    · exact ⟨a, by simp [heq], hend.1⟩
    · exact ⟨b, by simp [heq], hend.1⟩
  have edgeTarget_vertex :
      ∀ e : G.edgeFinset, ∃ v : V, v ∈ e.1 ∧ D.edgeTarget e = D.vertexPlacement v := by
    intro e
    rcases D.edgeArc_endpoints e with ⟨a, b, _hadj, heq, hend⟩
    rcases hend with hend | hend
    · exact ⟨b, by simp [heq], hend.2⟩
    · exact ⟨a, by simp [heq], hend.2⟩
  intro e₁ e₂ p he_ne hp₁ hp₂ hp_not_vertex hp_not_intersection
  have endpoint_in_vertex_ball :
      ∀ {e : G.edgeFinset},
        p = D.edgeSource e ∨ p = D.edgeTarget e → False := by
    intro e hp_endpoint
    rcases hp_endpoint with hp_source | hp_target
    · rcases edgeSource_vertex e with ⟨v, _hve, hv⟩
      have hpball : p ∈ Metric.ball (D.vertexPlacement v) (controlDisks.vertexRadius v) := by
        rw [hp_source, hv, Metric.mem_ball, dist_self]
        exact controlDisks.vertexRadius_pos v
      exact hp_not_vertex v hpball
    · rcases edgeTarget_vertex e with ⟨v, _hve, hv⟩
      have hpball : p ∈ Metric.ball (D.vertexPlacement v) (controlDisks.vertexRadius v) := by
        rw [hp_target, hv, Metric.mem_ball, dist_self]
        exact controlDisks.vertexRadius_pos v
      exact hp_not_vertex v hpball
  rcases carrier_endpoint_or_interior e₁ hp₁ with h1s | h1t_or_int
  · exact endpoint_in_vertex_ball (e := e₁) (Or.inl h1s)
  rcases h1t_or_int with h1t | h1int
  · exact endpoint_in_vertex_ball (e := e₁) (Or.inr h1t)
  rcases carrier_endpoint_or_interior e₂ hp₂ with h2s | h2t_or_int
  · rcases edgeSource_vertex e₂ with ⟨v, _hve, hv⟩
    have : D.vertexPlacement v ∈ D.edgeRelativeInterior e₁ := by
      simpa [h2s, hv] using h1int
    exact D.no_vertex_in_edge_interior v e₁ this
  rcases h2t_or_int with h2t | h2int
  · rcases edgeTarget_vertex e₂ with ⟨v, _hve, hv⟩
    have : D.vertexPlacement v ∈ D.edgeRelativeInterior e₁ := by
      simpa [h2t, hv] using h1int
    exact D.no_vertex_in_edge_interior v e₁ this
  · have hp_intersection : p ∈ D.intersectionPoints := by
      rw [D.intersectionPoints_spec]
      exact ⟨e₁, e₂, he_ne, h1int, h2int⟩
    let x : {q // q ∈ D.intersectionPoints} := ⟨p, hp_intersection⟩
    have hpball : p ∈ Metric.ball x.1 (controlDisks.intersectionRadius x) := by
      rw [Metric.mem_ball, dist_self]
      exact controlDisks.intersectionRadius_pos x
    exact hp_not_intersection x hpball
