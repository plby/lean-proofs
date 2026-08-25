import Util.IncidenceGeometry.ComplementComponent

open Classical
noncomputable section

lemma ConnectedSubsetContainedInUniqueComplementComponent
    (K T : Set (EuclideanSpace ℝ (Fin 2)))
    (hTne : T.Nonempty) (hTK : T ⊆ Kᶜ) (hTconn : IsConnected T) :
    ∃! C : Set (EuclideanSpace ℝ (Fin 2)), ComplementComponent K C ∧ T ⊆ C := by
  rcases hTne with ⟨x, hxT⟩
  have hxK : x ∈ Kᶜ := hTK hxT
  let C₀ : Set (EuclideanSpace ℝ (Fin 2)) := connectedComponentIn Kᶜ x
  have hTC₀ : T ⊆ C₀ :=
    hTconn.2.subset_connectedComponentIn hxT hTK
  have hxC₀ : x ∈ C₀ := mem_connectedComponentIn hxK
  have hC₀comp : ComplementComponent K C₀ := by
    refine ⟨⟨x, hxC₀⟩, connectedComponentIn_subset Kᶜ x, ?_, ?_⟩
    · exact (isConnected_connectedComponentIn_iff).2 hxK
    · intro C hCne hCK hCconn hC₀C
      have hxC : x ∈ C := hC₀C hxC₀
      exact hCconn.2.subset_connectedComponentIn hxC hCK
  refine ⟨C₀, ⟨hC₀comp, hTC₀⟩, ?_⟩
  intro C hC
  rcases hC with ⟨hCcomp, hTC⟩
  rcases hCcomp with ⟨hCne, hCK, hCconn, hCmax⟩
  have hxC : x ∈ C := hTC hxT
  have hC_subset_C₀ : C ⊆ C₀ :=
    hCconn.2.subset_connectedComponentIn hxC hCK
  have hC₀_subset_C : C₀ ⊆ C := by
    exact hCmax C₀ ⟨x, hxC₀⟩ (connectedComponentIn_subset Kᶜ x)
      ((isConnected_connectedComponentIn_iff).2 hxK) hC_subset_C₀
  exact le_antisymm hC_subset_C₀ hC₀_subset_C
