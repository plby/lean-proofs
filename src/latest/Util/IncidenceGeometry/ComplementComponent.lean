import Util.IncidenceGeometry.Basic

def ComplementComponent (K F : Set (EuclideanSpace ℝ (Fin 2))) : Prop :=
  F.Nonempty ∧ F ⊆ Kᶜ ∧ IsConnected F ∧
    ∀ C : Set (EuclideanSpace ℝ (Fin 2)),
      C.Nonempty → C ⊆ Kᶜ → IsConnected C → F ⊆ C → C ⊆ F
