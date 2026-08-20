import ErdosProblems.Erdos733.ST.Preamble

-- [TABLET NODE: ComplementComponent]
def ComplementComponent (K F : Set (EuclideanSpace ℝ (Fin 2))) : Prop :=
-- BODY
  F.Nonempty ∧ F ⊆ Kᶜ ∧ IsConnected F ∧
    ∀ C : Set (EuclideanSpace ℝ (Fin 2)),
      C.Nonempty → C ⊆ Kᶜ → IsConnected C → F ⊆ C → C ⊆ F
