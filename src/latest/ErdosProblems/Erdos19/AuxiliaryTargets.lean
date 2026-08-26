import ErdosProblems.Erdos19.ColorCoverCounting

/-! # Parity corrections at designated auxiliary vertices -/

namespace Erdos19

attribute [local instance] Classical.propDecidable

def auxiliaryTarget {V : Type*} (C : Set V) (z : V) : Set V :=
  if Even Cᶜ.ncard then Cᶜ else Cᶜ \ {z}

theorem auxiliaryTarget_subset {V : Type*} (C : Set V) (z : V) :
    auxiliaryTarget C z ⊆ Cᶜ := by
  unfold auxiliaryTarget
  split_ifs
  · exact Set.Subset.rfl
  · exact Set.sdiff_subset

theorem subset_auxiliaryTarget {V : Type*} (C : Set V) (z : V) :
    Cᶜ \ {z} ⊆ auxiliaryTarget C z := by
  unfold auxiliaryTarget
  split_ifs
  · exact Set.sdiff_subset
  · exact Set.Subset.rfl

theorem auxiliaryTarget_compl_subset {V : Type*} (C : Set V) (z : V) :
    (auxiliaryTarget C z)ᶜ ⊆ C ∪ {z} := by
  intro v hv
  by_cases hvC : v ∈ C
  · exact Or.inl hvC
  · by_cases hvz : v = z
    · exact Or.inr hvz
    · exact (hv (subset_auxiliaryTarget C z ⟨hvC, hvz⟩)).elim

theorem auxiliaryTarget_even {V : Type*} [Fintype V] (C : Set V) (z : V) (hz : z ∉ C) :
    Even (auxiliaryTarget C z).ncard := by
  unfold auxiliaryTarget
  split_ifs with heven
  · exact heven
  · rw [Set.ncard_sdiff_singleton_of_mem hz, Nat.even_iff]
    have h := Nat.not_even_iff.mp heven
    omega

theorem auxiliaryTarget_omission_bound {V I : Type*} [Fintype I]
    (C : I → Set V) (f : I → V) (hf : Function.Injective f) (v : V) :
    (∑ i : I, if v ∈ auxiliaryTarget (C i) (f i) then 0 else 1) ≤
      (∑ i : I, if v ∈ C i then 1 else 0) + if v ∈ Set.range f then 1 else 0 := by
  classical
  have hper : ∀ i : I, (if v ∈ auxiliaryTarget (C i) (f i) then 0 else 1) ≤
      (if v ∈ C i then 1 else 0) + (if f i = v then 1 else 0) := by
    intro i
    by_cases hv : v ∈ auxiliaryTarget (C i) (f i)
    · simp only [hv, ↓reduceIte, Nat.zero_le]
    · have h := auxiliaryTarget_compl_subset (C i) (f i) hv
      rcases h with h | h
      · simp only [hv, h, ↓reduceIte]
        omega
      · have hz : f i = v := h.symm
        rw [if_neg hv, if_pos hz]
        omega
  have hfiber : (∑ i : I, if f i = v then 1 else 0) ≤ if v ∈ Set.range f then 1 else 0 := by
    by_cases hv : v ∈ Set.range f
    · rw [if_pos hv]
      simp only [Finset.sum_boole]
      apply Finset.card_le_one.mpr
      intro i hi j hj
      exact hf ((Finset.mem_filter.mp hi).2.trans (Finset.mem_filter.mp hj).2.symm)
    · rw [if_neg hv]
      have hne : ∀ i, f i ≠ v := fun i h ↦ hv ⟨i, h⟩
      simp only [hne, ↓reduceIte, Finset.sum_const_zero, le_refl]
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset I)) ↦ hper i)
  rw [Finset.sum_add_distrib] at hs
  exact hs.trans (Nat.add_le_add_left hfiber _)

#print axioms auxiliaryTarget_omission_bound

end Erdos19
