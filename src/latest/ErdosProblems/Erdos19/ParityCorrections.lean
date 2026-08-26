import ErdosProblems.Erdos19.AuxiliaryTargets

/-! # Distinct parity corrections with arbitrary forbidden sets -/

namespace Erdos19

attribute [local instance] Classical.propDecidable

theorem exists_distinct_corrections_avoiding
    {V I : Type*} [Fintype V] [Fintype I] (U : Set V) (C : I → Set V)
    (hroom : ∀ i, Fintype.card I + (C i).ncard ≤ U.ncard) :
    ∃ f : I → V, Function.Injective f ∧ (∀ i, f i ∈ U ∧ f i ∉ C i) := by
  classical
  obtain ⟨f, hf, hmem⟩ := exists_injective_mem_of_card_le
    (fun i ↦ (U \ C i).toFinset) (fun i ↦ by
      rw [Set.toFinset_card, Set.fintypeCard_eq_ncard]
      have h := hroom i
      have hsub := Set.ncard_le_ncard_sdiff_add_ncard U (C i)
      omega)
  refine ⟨f, hf, fun i ↦ ?_⟩
  have h : f i ∈ U \ C i := Set.mem_toFinset.mp (hmem i)
  exact h

theorem auxiliaryTarget_compl_ncard_le {V : Type*} [Fintype V]
    (C : Set V) (z : V) : (auxiliaryTarget C z)ᶜ.ncard ≤ C.ncard + 1 := by
  exact (Set.ncard_le_ncard (auxiliaryTarget_compl_subset C z)).trans
    (by simpa only [Set.ncard_singleton] using Set.ncard_union_le C {z})

theorem auxiliaryTarget_omission_bound_in_set {V I : Type*} [Fintype I]
    (U : Set V) (C : I → Set V) (f : I → V) (hf : Function.Injective f)
    (hU : ∀ i, f i ∈ U) (v : V) :
    (∑ i : I, if v ∈ auxiliaryTarget (C i) (f i) then 0 else 1) ≤
      (∑ i : I, if v ∈ C i then 1 else 0) + if v ∈ U then 1 else 0 := by
  have h := auxiliaryTarget_omission_bound C f hf v
  have hindicator : (if v ∈ Set.range f then 1 else 0 : ℕ) ≤
      if v ∈ U then 1 else 0 := by
    by_cases hv : v ∈ Set.range f
    · obtain ⟨i, rfl⟩ := hv
      simp [hU i]
    · simp only [hv, ↓reduceIte, Nat.zero_le]
  exact h.trans (Nat.add_le_add_left hindicator _)

#print axioms exists_distinct_corrections_avoiding
#print axioms auxiliaryTarget_omission_bound_in_set

end Erdos19
