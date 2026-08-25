import Util.IncidenceGeometry.OrdinaryPolygonalDrawing

open Classical
noncomputable section

lemma CrossingFreeEdgeInteriorDisjoint {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet]
    (D : OrdinaryPolygonalDrawing G) (hD : D.crossingSet.card = 0) :
    ∀ ⦃e₁ e₂ : G.edgeFinset⦄ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
      e₁ ≠ e₂ →
        p ∈ (D.edgeArc e₁).relativeInterior →
          p ∈ (D.edgeArc e₂).relativeInterior → False := by
  intro e₁ e₂ p hne hp₁ hp₂
  have hp_cross : p ∈ D.crossingSet := by
    rw [D.crossingSet_spec]
    exact ⟨e₁, e₂, hne, hp₁, hp₂⟩
  have h_empty : D.crossingSet = ∅ := Finset.card_eq_zero.mp hD
  have h_not : p ∉ D.crossingSet := by
    simp [h_empty]
  exact h_not hp_cross
