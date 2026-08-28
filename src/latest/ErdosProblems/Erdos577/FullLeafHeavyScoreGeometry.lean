import ErdosProblems.Erdos577.FullLeafHeavyCoreSplit

/-! Exact complements for a core insertion in any actual triangle chain. -/

namespace Erdos577.FullLeafHeavy

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

lemma insertion_complement (c : TriangleChain G) {a j : Finset V}
    (ha : a ∈ c.blocks) (hj : j ∈ c.blocks) (haj : a ≠ j) {v : V} (hv : v ∈ j) :
    (c.remainder ∪ (a ∪ j)) \ insert v (c.triangle ∪ a) =
      insert c.terminal (j.erase v) := by
  have hKJ : Disjoint (c.triangle ∪ a) j := disjoint_union_left.mpr
    ⟨c.triangle_disjoint_block hj, c.property.blocks_disjoint ha hj haj⟩
  have hxv : c.terminal ≠ v := fun hh ↦ c.terminal_not_mem_block hj (hh.symm ▸ hv)
  ext w
  by_cases hwx : w = c.terminal
  · subst w
    change (c.terminal ∈ (insert c.terminal c.triangle ∪ (a ∪ j)) \
      insert v (c.triangle ∪ a)) ↔ c.terminal ∈ insert c.terminal (j.erase v)
    simp only [mem_sdiff, mem_union, mem_insert, true_or, mem_erase,
      c.property.terminal_not_mem, c.terminal_not_mem_block ha, hxv, false_or,
      not_false_eq_true, and_self]
  · have hjK : w ∈ j → w ∉ c.triangle ∪ a := fun hh hK ↦ disjoint_left.mp hKJ hK hh
    change (w ∈ (insert c.terminal c.triangle ∪ (a ∪ j)) \
      insert v (c.triangle ∪ a)) ↔ w ∈ insert c.terminal (j.erase v)
    simp only [mem_sdiff, mem_union, mem_insert, mem_erase, hwx, false_or] at hjK ⊢
    tauto

lemma insertion_subset (c : TriangleChain G) {a j : Finset V} {v : V} (hv : v ∈ j) :
    insert v (c.triangle ∪ a) ⊆ c.remainder ∪ (a ∪ j) :=
  insert_subset (mem_union_right _ (mem_union_right _ hv)) (union_subset
    (fun _ hh ↦ mem_union_left _ (mem_insert_of_mem hh))
    (fun _ hh ↦ mem_union_right _ (mem_union_left _ hh)))

lemma insertion_remainder_card (c : TriangleChain G) {j : Finset V}
    (hj : j ∈ c.blocks) {v : V} (hv : v ∈ j) : (insert c.terminal (j.erase v)).card = 4 := by
  have hout : c.terminal ∉ j.erase v := fun hh ↦ c.terminal_not_mem_block hj (mem_erase.mp hh).2
  rw [card_insert_of_notMem hout, card_erase_of_mem hv, (c.property.blocks_quad j hj).card]

end Erdos577.FullLeafHeavy
