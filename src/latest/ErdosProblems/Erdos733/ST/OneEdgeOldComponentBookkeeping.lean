import ErdosProblems.Erdos733.ST.ComplementComponent
import ErdosProblems.Erdos733.ST.ComplementComponentAbsorbsConnectedSubset
import ErdosProblems.Erdos733.ST.ComplementComponentDisjointUnionRight
import ErdosProblems.Erdos733.ST.ConnectedSubsetContainedInUniqueComplementComponent

open Classical
noncomputable section

-- [TABLET NODE: OneEdgeOldComponentBookkeeping]
lemma OneEdgeOldComponentBookkeeping
    (A : Set (EuclideanSpace ℝ (Fin 2)))
    (a b : EuclideanSpace ℝ (Fin 2))
    (hab : a ≠ b)
    (haA : a ∈ A) (hbA : b ∈ A)
    (hNewInteriorDisjoint : Disjoint (openSegment ℝ a b) A) :
    ∃ Csigma : Set (EuclideanSpace ℝ (Fin 2)),
      ComplementComponent A Csigma ∧
        openSegment ℝ a b ⊆ Csigma ∧
        (∀ D : Set (EuclideanSpace ℝ (Fin 2)),
          ComplementComponent A D → openSegment ℝ a b ⊆ D → D = Csigma) ∧
        ∀ C : Set (EuclideanSpace ℝ (Fin 2)),
          ComplementComponent A C → C ≠ Csigma →
            Disjoint C (segment ℝ a b) ∧
              ComplementComponent (A ∪ segment ℝ a b) C := by
-- BODY
  have hsigma_ne : (openSegment ℝ a b).Nonempty :=
    ⟨midpoint ℝ a b, midpoint_mem_openSegment (𝕜 := ℝ) a b⟩
  have hsigma_subset_old_compl : openSegment ℝ a b ⊆ Aᶜ := by
    intro x hx_sigma hxA
    exact (Set.disjoint_left.mp hNewInteriorDisjoint) hx_sigma hxA
  have hsigma_connected : IsConnected (openSegment ℝ a b) :=
    (convex_openSegment (𝕜 := ℝ) a b).isConnected hsigma_ne
  rcases ConnectedSubsetContainedInUniqueComplementComponent
      A (openSegment ℝ a b) hsigma_ne hsigma_subset_old_compl hsigma_connected with
    ⟨Csigma, hCsigma, hunique⟩
  refine ⟨Csigma, hCsigma.1, hCsigma.2, ?_, ?_⟩
  · intro D hD hD_contains
    exact hunique D ⟨hD, hD_contains⟩
  · intro C hC hC_ne
    have hC_disjoint_open : Disjoint C (openSegment ℝ a b) := by
      rw [Set.disjoint_left]
      intro x hxC hx_sigma
      have hsigma_subset_C : openSegment ℝ a b ⊆ C :=
        ComplementComponentAbsorbsConnectedSubset A C (openSegment ℝ a b)
          hC hsigma_ne hsigma_subset_old_compl hsigma_connected ⟨x, hxC, hx_sigma⟩
      exact hC_ne (hunique C ⟨hC, hsigma_subset_C⟩)
    have hC_disjoint_segment : Disjoint C (segment ℝ a b) := by
      rw [← insert_endpoints_openSegment (𝕜 := ℝ) a b]
      rw [Set.disjoint_left]
      intro x hxC hx_segment
      rcases hx_segment with rfl | hx_segment
      · exact hC.2.1 hxC haA
      · rcases hx_segment with rfl | hx_sigma
        · exact hC.2.1 hxC hbA
        · exact (Set.disjoint_left.mp hC_disjoint_open) hxC hx_sigma
    exact ⟨hC_disjoint_segment,
      ComplementComponentDisjointUnionRight A (segment ℝ a b) C hC hC_disjoint_segment⟩
