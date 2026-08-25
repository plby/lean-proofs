import Util.IncidenceGeometry.PolygonalPath

def PolygonallyPathConnected (S : Set (EuclideanSpace ℝ (Fin 2))) : Prop :=
  ∀ ⦃p q : EuclideanSpace ℝ (Fin 2)⦄,
    p ∈ S → q ∈ S →
      ∃ γ : PolygonalPath,
        γ.source = p ∧ γ.target = q ∧ γ.carrier ⊆ S
