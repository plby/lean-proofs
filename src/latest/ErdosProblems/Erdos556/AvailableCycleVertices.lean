import ErdosProblems.Erdos556.CycleVertexSets

/-!
# Available common neighbors on the cycle

If few common neighbors lie off the cycle, deleting those vertices and
a fixed prefix still leaves a linear-size set of available cycle vertices.
-/

namespace Erdos556

open SimpleGraph Finset

theorem exists_available_cycle_vertices {V : Type*} [DecidableEq V] {G : SimpleGraph V} {z : V}
    (c : G.Walk z z) (W : Finset V) (N K Q M : ℕ) (hM : M ≤ c.length)
    (hsize : N ≤ K * W.card) (hN : 2 * K * (Q + M + 1) ≤ N)
    (hoff : (W \ c.support.toFinset).card < Q) :
    ∃ U : Finset V, U ⊆ W ∧ (∀ x ∈ U, x ∈ c.support) ∧
      (∀ i, i ≤ M → c.getVert i ∉ U) ∧ N ≤ 2 * K * U.card := by
  let P := (c.take M).support.toFinset
  let E := W \ c.support.toFinset
  let U := (W ∩ c.support.toFinset) \ P
  have hP : P.card ≤ M + 1 := by
    have h := List.toFinset_card_le (c.take M).support
    simpa only [Walk.length_support, Walk.take_length, min_eq_left hM] using h
  have hcover : W ⊆ U ∪ E ∪ P := by
    intro x hxW
    by_cases hxP : x ∈ P
    · exact mem_union_right _ hxP
    by_cases hxC : x ∈ c.support.toFinset
    · exact mem_union_left _ (mem_union_left _ (mem_sdiff.mpr ⟨mem_inter.mpr ⟨hxW, hxC⟩, hxP⟩))
    · exact mem_union_left _ (mem_union_right _ (mem_sdiff.mpr ⟨hxW, hxC⟩))
  have hcount : W.card ≤ U.card + Q + M + 1 := by
    have h₁ := card_le_card hcover
    have h₂ := card_union_le (U ∪ E) P
    have h₃ := card_union_le U E
    change E.card < Q at hoff
    omega
  refine ⟨U, (sdiff_subset).trans inter_subset_left, ?_, ?_, ?_⟩
  · intro x hx
    exact List.mem_toFinset.mp (mem_inter.mp (mem_sdiff.mp hx).1).2
  · intro i hi hmem
    have hp : c.getVert i ∈ P := List.mem_toFinset.mpr
      ((mem_support_take_iff c M hM).mpr ⟨i, hi, rfl⟩)
    exact (mem_sdiff.mp hmem).2 hp
  · have hmul := Nat.mul_le_mul_left K hcount
    nlinarith only [hsize, hN, hmul]

#print axioms exists_available_cycle_vertices

end Erdos556
