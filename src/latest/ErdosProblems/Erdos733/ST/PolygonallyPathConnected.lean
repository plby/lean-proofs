import ErdosProblems.Erdos733.ST.PolygonalPath

-- [TABLET NODE: PolygonallyPathConnected]
def PolygonallyPathConnected (S : Set (EuclideanSpace ℝ (Fin 2))) : Prop :=
-- BODY
  ∀ ⦃p q : EuclideanSpace ℝ (Fin 2)⦄,
    p ∈ S → q ∈ S →
      ∃ γ : PolygonalPath,
        γ.source = p ∧ γ.target = q ∧ γ.carrier ⊆ S
