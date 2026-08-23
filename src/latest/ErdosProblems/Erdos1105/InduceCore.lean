import ErdosProblems.Erdos1105.PathNeighborCounts

namespace Erdos1105

open SimpleGraph Finset

lemma degreeWithin_induce_image {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (T : Finset V) (S : Finset (T : Set V)) (v : (T : Set V)) :
    degreeWithin (G.induce (T : Set V)) S v =
      degreeWithin G (S.image Subtype.val) v.val := by
  classical
  unfold degreeWithin
  have heq : (S.filter ((G.induce (T : Set V)).Adj v)).image Subtype.val =
      (S.image Subtype.val).filter (G.Adj v.val) := by
    ext w
    simp only [mem_image, mem_filter, induce_adj]
    constructor
    · rintro ⟨z, ⟨hz, hadj⟩, rfl⟩
      exact ⟨⟨z, hz, rfl⟩, hadj⟩
    · rintro ⟨⟨z, hz, rfl⟩, hadj⟩
      exact ⟨z, ⟨hz, hadj⟩, rfl⟩
  rw [← heq, card_image_of_injective _ Subtype.val_injective]
  rfl

/-- Restriction to a vertex set containing the core preserves the core. -/
theorem vertexCore_induce_image {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (d : ℕ) (T : Finset V) (hsub : vertexCore G d ⊆ T) :
    (vertexCore (G.induce (T : Set V)) d).image Subtype.val = vertexCore G d := by
  classical
  apply Subset.antisymm
  · apply subset_vertexCore
    intro v hv
    obtain ⟨w, hw, rfl⟩ := mem_image.mp hv
    rw [← degreeWithin_induce_image]
    exact vertexCore_degree _ _ hw
  · let S : Finset (T : Set V) := univ.filter (fun v ↦ v.val ∈ vertexCore G d)
    have hS : S.image Subtype.val = vertexCore G d := by
      ext v
      simp only [mem_image, S, mem_filter, mem_univ, true_and]
      constructor
      · rintro ⟨w, hw, rfl⟩
        exact hw
      · intro hv
        exact ⟨⟨v, hsub hv⟩, hv, rfl⟩
    have hSsub : S ⊆ vertexCore (G.induce (T : Set V)) d := by
      apply subset_vertexCore
      intro v hv
      rw [degreeWithin_induce_image, hS]
      exact vertexCore_degree G d (mem_filter.mp hv).2
    rw [← hS]
    exact image_subset_image hSsub

end Erdos1105

#print axioms Erdos1105.vertexCore_induce_image
