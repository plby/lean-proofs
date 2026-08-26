import ErdosProblems.Erdos19.Completion

/-! # Choosing distinct parity corrections for matching targets -/

namespace Erdos19

open Finset

attribute [local instance] Classical.propDecidable

theorem exists_even_targets_with_distinct_corrections
    {V I : Type*} [Fintype V] [Fintype I] (U : Set V) (C : I → Set V)
    (hCU : ∀ i, C i ⊆ U)
    (hroom : ∀ i, Fintype.card I + (C i).ncard ≤ U.ncard) :
    ∃ A : I → Set V,
      (∀ i, Even (A i).ncard ∧ A i ⊆ (C i)ᶜ ∧ (A i)ᶜ ⊆ U ∧
        (A i)ᶜ.ncard ≤ (C i).ncard + 1) ∧
      (∀ v, (∑ i : I, if v ∈ A i then 0 else 1) ≤
        (∑ i : I, if v ∈ C i then 1 else 0) + if v ∈ U then 1 else 0) := by
  classical
  obtain ⟨f, hf, hmem⟩ := exists_injective_mem_of_card_le
    (fun i ↦ (U \ C i).toFinset) (fun i ↦ by
      rw [Set.toFinset_card, Set.fintypeCard_eq_ncard, Set.ncard_sdiff (hCU i)]
      have h := hroom i
      omega)
  have hfU : ∀ i, f i ∈ U := fun i ↦ (Set.mem_toFinset.mp (hmem i)).1
  have hfC : ∀ i, f i ∉ C i := fun i ↦ (Set.mem_toFinset.mp (hmem i)).2
  let A : I → Set V := fun i ↦ if Even (C i)ᶜ.ncard then (C i)ᶜ else (C i)ᶜ \ {f i}
  have hAsub : ∀ i, A i ⊆ (C i)ᶜ := by
    intro i
    dsimp only [A]
    split_ifs
    · exact Set.Subset.rfl
    · exact Set.sdiff_subset
  have hAsup : ∀ i, (C i)ᶜ \ {f i} ⊆ A i := by
    intro i
    dsimp only [A]
    split_ifs
    · exact Set.sdiff_subset
    · exact Set.Subset.rfl
  have hcompl : ∀ i, (A i)ᶜ ⊆ C i ∪ {f i} := by
    intro i v hv
    by_cases hvC : v ∈ C i
    · exact Or.inl hvC
    · right
      by_contra hvf
      exact hv (hAsup i ⟨hvC, hvf⟩)
  refine ⟨A, ?_, ?_⟩
  · intro i
    refine ⟨?_, hAsub i, ?_, ?_⟩
    · dsimp only [A]
      split_ifs with heven
      · exact heven
      · rw [Set.ncard_sdiff_singleton_of_mem (hfC i)]
        rw [Nat.even_iff]
        have h := Nat.not_even_iff.mp heven
        omega
    · intro v hv
      rcases hcompl i hv with hvC | hvf
      · exact hCU i hvC
      · rw [Set.mem_singleton_iff] at hvf
        exact hvf ▸ hfU i
    · exact (Set.ncard_le_ncard (hcompl i)).trans (by
        simpa only [Set.ncard_singleton] using Set.ncard_union_le (C i) {f i})
  · intro v
    have hper : ∀ i : I, (if v ∈ A i then 0 else 1) ≤
        (if v ∈ C i then 1 else 0) + (if v = f i then 1 else 0) := by
      intro i
      by_cases hvA : v ∈ A i
      · simp only [hvA, ↓reduceIte, zero_le]
      · have h := hcompl i hvA
        rcases h with h | h
        · simp only [hvA, h, ↓reduceIte, le_add_iff_nonneg_right, zero_le]
        · have heq : v = f i := h
          rw [if_neg hvA, if_pos heq]
          omega
    have hfiber : (∑ i : I, if v = f i then 1 else 0) ≤ if v ∈ U then 1 else 0 := by
      by_cases hvU : v ∈ U
      · rw [if_pos hvU]
        simp only [sum_boole]
        apply card_le_one.mpr
        intro i hi j hj
        apply hf
        exact (mem_filter.mp hi).2.symm.trans (mem_filter.mp hj).2
      · rw [if_neg hvU]
        have hn : ∀ i, v ≠ f i := fun i h ↦ hvU (h ▸ hfU i)
        simp only [hn, ↓reduceIte, sum_const_zero, le_refl]
    have hs := sum_le_sum (fun i (_ : i ∈ (univ : Finset I)) ↦ hper i)
    rw [sum_add_distrib] at hs
    exact hs.trans (Nat.add_le_add_left hfiber _)

#print axioms exists_even_targets_with_distinct_corrections

end Erdos19
