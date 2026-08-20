import ErdosProblems.Erdos733.ST.ComplementComponent

open Classical
noncomputable section

-- [TABLET NODE: ComplementComponentAbsorbsConnectedSubset]
lemma ComplementComponentAbsorbsConnectedSubset
    (K C T : Set (EuclideanSpace ℝ (Fin 2))) :
    ComplementComponent K C →
      T.Nonempty → T ⊆ Kᶜ → IsConnected T →
        (C ∩ T).Nonempty → T ⊆ C := by
-- BODY
  intro hC hTne hTK hTconn hmeet
  rcases hC with ⟨_hCne, hCK, hCconn, hCmax⟩
  have hUnionNonempty : (C ∪ T).Nonempty := hTne.mono (by
    intro x hx
    exact Or.inr hx)
  have hUnionSubset : C ∪ T ⊆ Kᶜ := by
    intro x hx
    rcases hx with hxC | hxT
    · exact hCK hxC
    · exact hTK hxT
  have hUnionConnected : IsConnected (C ∪ T) :=
    IsConnected.union hmeet hCconn hTconn
  have hCUnion : C ⊆ C ∪ T := by
    intro x hx
    exact Or.inl hx
  have hUnionC : C ∪ T ⊆ C :=
    hCmax (C ∪ T) hUnionNonempty hUnionSubset hUnionConnected hCUnion
  intro x hxT
  exact hUnionC (Or.inr hxT)
