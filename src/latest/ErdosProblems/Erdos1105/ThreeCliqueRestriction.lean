import ErdosProblems.Erdos1105.ThreeCliqueCycle

namespace Erdos1105

open SimpleGraph Finset

/-- Remove one distinguished vertex from the universal part of the join,
transporting the remaining vertices along an injection. -/
theorem threeCliqueJoin_remove_vertex {V W : Type*} [Fintype V] [Fintype W]
    (f : V ↪ W) (u : W) (havoid : ∀ v, f v ≠ u)
    (hcover : ∀ w, w ≠ u → ∃ v, f v = w) {A T : Finset W} {d : ℕ}
    (hu : u ∈ A) (hA : A.card = d) (hT : T.card = 3) (hAT : Disjoint A T) :
    ∃ A' T' : Finset V, A'.card = d - 1 ∧ T'.card = 3 ∧ Disjoint A' T' ∧
      threeCliqueJoin A' T' ≤ (threeCliqueJoin A T).comap f := by
  classical
  let A' : Finset V := univ.filter (fun v ↦ f v ∈ A)
  let T' : Finset V := univ.filter (fun v ↦ f v ∈ T)
  have huT : u ∉ T := fun h ↦ Finset.disjoint_left.mp hAT hu h
  have hAim : A'.image f = A.erase u := by
    ext w
    constructor
    · intro hw
      obtain ⟨v, hv, rfl⟩ := mem_image.mp hw
      exact mem_erase.mpr ⟨havoid v, (mem_filter.mp hv).2⟩
    · intro hw
      obtain ⟨v, rfl⟩ := hcover w (mem_erase.mp hw).1
      exact mem_image.mpr ⟨v, mem_filter.mpr ⟨mem_univ _, (mem_erase.mp hw).2⟩, rfl⟩
  have hTim : T'.image f = T := by
    ext w
    constructor
    · intro hw
      obtain ⟨v, hv, rfl⟩ := mem_image.mp hw
      exact (mem_filter.mp hv).2
    · intro hw
      obtain ⟨v, rfl⟩ := hcover w (fun h ↦ huT (h ▸ hw))
      exact mem_image.mpr ⟨v, mem_filter.mpr ⟨mem_univ _, hw⟩, rfl⟩
  refine ⟨A', T', ?_, ?_, ?_, ?_⟩
  · rw [← card_image_of_injective A' f.injective, hAim, card_erase_of_mem hu, hA]
  · rw [← card_image_of_injective T' f.injective, hTim, hT]
  · exact Finset.disjoint_left.mpr (fun _ ha ht ↦
      Finset.disjoint_left.mp hAT (mem_filter.mp ha).2 (mem_filter.mp ht).2)
  · intro v w h
    refine ⟨f.injective.ne h.1, ?_⟩
    rcases h.2 with hv | hw | htw
    · exact Or.inl (mem_filter.mp hv).2
    · exact Or.inr (Or.inl (mem_filter.mp hw).2)
    · exact Or.inr (Or.inr ⟨(mem_filter.mp htw.1).2, (mem_filter.mp htw.2).2⟩)

end Erdos1105

#print axioms Erdos1105.threeCliqueJoin_remove_vertex
