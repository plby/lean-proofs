import ErdosProblems.Erdos577.Counting

/-! More than one contact per target vertex forces two distinct source neighbors at one vertex. -/

namespace Erdos577

open Finset

variable {V : Type*} {G : SimpleGraph V} [DecidableRel G.Adj]

lemma exists_common_pair_of_contacts (s t : Finset V) (h : t.card < contacts G s t) :
    ∃ u ∈ t, ∃ v ∈ s, ∃ w ∈ s, v ≠ w ∧ G.Adj v u ∧ G.Adj w u := by
  have hex : ∃ u ∈ t, 2 ≤ degreeIn G u s := by
    by_contra! hn
    have hbound : contacts G t s ≤ t.card := by
      calc
        _ ≤ ∑ _ ∈ t, 1 := sum_le_sum fun u hu ↦ by have hh := hn u hu; omega
        _ = t.card := by simp
    rw [contacts_comm] at h
    omega
  obtain ⟨u, hu, htwo⟩ := hex
  obtain ⟨v, hv, w, hw, hvw⟩ := one_lt_card.mp (by
    change 1 < degreeIn G u s
    omega)
  exact ⟨u, hu, v, (mem_filter.mp hv).1, w, (mem_filter.mp hw).1, hvw,
    (mem_filter.mp hv).2.symm, (mem_filter.mp hw).2.symm⟩

end Erdos577
