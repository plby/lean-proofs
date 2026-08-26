import ErdosProblems.Erdos556.CycleVertexSets
import ErdosProblems.Erdos556.ParityBlocks

/-!
# Selecting the interior cycle reservoir

A linear-size set of available cycle vertices, all beyond a fixed
prefix, contains any prescribed constant number of vertices of the
same parity within a uniformly bounded interval.
-/

namespace Erdos556

open SimpleGraph Finset

theorem exists_cycle_parity_block {V : Type*} [DecidableEq V] {G : SimpleGraph V} {z : V}
    (c : G.Walk z z) (hc : c.IsCycle) (W : Finset V) (hW : ∀ x ∈ W, x ∈ c.support)
    (M N K L : ℕ) (hK : 0 < K) (hL : 0 < L) (hN : 8 * K * L ≤ N)
    (hcN : c.length ≤ N) (hsize : N ≤ 2 * K * W.card)
    (hoff : ∀ i, i ≤ M → c.getVert i ∉ W) :
    ∃ B : Finset ℕ, B.card = L ∧
      (∀ i ∈ B, M < i ∧ i < c.length ∧ c.getVert i ∈ W) ∧
      ∀ i ∈ B, ∀ j ∈ B, i % 2 = j % 2 ∧ j < i + 8 * K * L := by
  let S := cycleIndexSet c W
  have hScard : S.card = W.card := cycleIndexSet_card c hc W hW
  have hS (i : ℕ) (hi : i ∈ S) : i < N :=
    (mem_range.mp (mem_filter.mp hi).1).trans_le hcN
  have hdiv : N / (2 * K) ≤ W.card := by
    have h := Nat.div_le_div_right hsize (c := 2 * K)
    simpa only [Nat.mul_div_cancel_left W.card (by omega : 0 < 2 * K)] using h
  have hcount : 2 * (N / (8 * K * L) + 1) * (L - 1) < S.card := by
    rw [hScard]
    exact (parity_block_count_bound N K L hK hL hN).trans_le hdiv
  obtain ⟨B, hBS, hB, hpar⟩ := exists_same_parity_block S N (8 * K * L) L
    (by positivity) hS hcount
  refine ⟨B, hB, ?_, hpar⟩
  intro i hi
  obtain ⟨hiN, hiW⟩ := mem_filter.mp (hBS hi)
  exact ⟨by by_contra h; exact hoff i (by omega) hiW, mem_range.mp hiN, hiW⟩

#print axioms exists_cycle_parity_block

end Erdos556
