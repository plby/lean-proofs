import Mathlib

/- Ported from Lean 4.31.0 to 4.33.0; imports and elaboration options adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos489

/-- A finite map has a transversal: one representative of every value in its
image, contained in the original set and with injective restricted map. -/
theorem Finset.exists_subset_injOn_card_eq_image
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (S : Finset α) (f : α → β) :
    ∃ T : Finset α, T ⊆ S ∧ Set.InjOn f (T : Set α) ∧
      T.card = (S.image f).card := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨∅, by simp⟩
  | insert a s ha ih =>
      obtain ⟨T, hTs, hinj, hcard⟩ := ih
      by_cases him : f a ∈ s.image f
      · refine ⟨T, hTs.trans (Finset.subset_insert a s), hinj, ?_⟩
        rw [Finset.image_insert, Finset.card_insert_of_mem him]
        exact hcard
      · refine ⟨insert a T, ?_, ?_, ?_⟩
        · intro y hy
          rcases Finset.mem_insert.mp hy with rfl | hyT
          · exact Finset.mem_insert_self _ _
          · exact Finset.mem_insert_of_mem (hTs hyT)
        · intro y hy z hz heq
          rcases Finset.mem_insert.mp hy with rfl | hyT
          · rcases Finset.mem_insert.mp hz with rfl | hzT
            · rfl
            · exfalso
              apply him
              exact Finset.mem_image.mpr ⟨z, hTs hzT, heq.symm⟩
          · rcases Finset.mem_insert.mp hz with rfl | hzT
            · exfalso
              apply him
              exact Finset.mem_image.mpr ⟨y, hTs hyT, heq⟩
            · exact hinj hyT hzT heq
        · rw [Finset.card_insert_of_notMem]
          · rw [Finset.image_insert, Finset.card_insert_of_notMem him, hcard]
          · intro haT
            exact ha (hTs haT)

end Erdos489
