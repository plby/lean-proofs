import ErdosProblems.Erdos556.JoinedBucketBounds

/-! Counting vertices assigned to large monochromatic clique cores. -/

namespace Erdos556

open SimpleGraph Finset

theorem clique_core_capacity_bound {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I]
    (G : I → SimpleGraph V) (A : I → Finset V) (r : ℕ) (hr : 1 ≤ r)
    (hA : ∀ i, r + 1 ≤ (A i).card) (hclique : ∀ i, (G i).IsClique (A i : Set V))
    (hno : ∀ i, ¬ cycleGraph (2 * r + 1) ⊑ G i)
    (hcover : ∀ x : V, ∃ i, x ∈ A i ∨ ∀ a ∈ A i, (G i).Adj x a) :
    Fintype.card V ≤ 2 * r * Fintype.card I := by
  classical
  let S : I → Finset V := fun i => univ.filter (fun x => x ∈ A i ∨ ∀ a ∈ A i, (G i).Adj x a)
  have hAS (i : I) : A i ⊆ S i := by
    intro x hx
    exact mem_filter.mpr ⟨mem_univ _, Or.inl hx⟩
  have hjoin (i : I) : ∀ a ∈ A i, ∀ x ∈ S i, a ≠ x → (G i).Adj a x := by
    intro a ha x hx hax
    rcases (mem_filter.mp hx).2 with hxA | hx
    · exact hclique i ha hxA hax
    · exact (hx a ha).symm
  have hsize (i : I) : (S i).card ≤ 2 * r := by
    by_contra h
    exact hno i ((cycleGraph_isContained_iff (by omega : 2 < 2 * r + 1)).mpr
      (exists_odd_cycle_in_large_joined_bucket (G i) (A i) (S i) r hr (hAS i) (hA i)
        (by omega) (hjoin i)))
  have hunion : univ.biUnion S = (univ : Finset V) := by
    apply eq_univ_iff_forall.mpr
    intro x
    obtain ⟨i, hi⟩ := hcover x
    exact mem_biUnion.mpr ⟨i, mem_univ _, mem_filter.mpr ⟨mem_univ _, hi⟩⟩
  calc
    Fintype.card V = (univ.biUnion S).card := by rw [hunion, card_univ]
    _ ≤ ∑ i, (S i).card := card_biUnion_le
    _ ≤ ∑ _i : I, 2 * r := sum_le_sum fun i _ => hsize i
    _ = 2 * r * Fintype.card I := by simp [Nat.mul_comm]

#print axioms clique_core_capacity_bound

end Erdos556
