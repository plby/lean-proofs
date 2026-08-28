import ErdosProblems.Erdos577.TripleHeavyBlock

/-! Eleven contacts from three rows select a common neighbor with a complete replacement. -/

namespace Erdos577

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem three_rows_choose_complete_replacement {a : Finset V} (hcl : G.IsNClique 4 a)
    (x r y : V) (hheavy : 11 ≤ degreeIn G x a + degreeIn G r a + degreeIn G y a) :
    ∃ u ∈ a, G.Adj x u ∧ G.Adj r u ∧ G.IsNClique 4 (insert y (a.erase u)) := by
  have hx4 := degreeIn_le_card G x a
  have hr4 := degreeIn_le_card G r a
  have hy4 := degreeIn_le_card G y a
  rw [hcl.card_eq] at hx4 hr4 hy4
  by_cases hy : degreeIn G y a = 4
  · have hex : ∃ u ∈ a, G.Adj x u ∧ G.Adj r u := by
      by_contra hn
      have hb := degree_pair_le_card x r a (fun u hu he ↦ hn ⟨u, hu, he⟩)
      rw [hcl.card_eq] at hb
      omega
    obtain ⟨u, hu, hxu, hru⟩ := hex
    refine ⟨u, hu, hxu, hru, hcl.insert_erase ?_ hu⟩
    intro w hw
    exact (degreeIn_eq_card_iff y a).mp (hy.trans hcl.card_eq.symm) w (mem_sdiff.mp hw).1
  · have hx : degreeIn G x a = 4 := by omega
    have hr : degreeIn G r a = 4 := by omega
    have hy3 : degreeIn G y a = 3 := by omega
    have hmiss : ∃ u ∈ a, ¬G.Adj y u := by
      by_contra! hh
      have he := (degreeIn_eq_card_iff y a).mpr hh
      rw [hcl.card_eq] at he
      exact hy he
    obtain ⟨u, hu, hyu⟩ := hmiss
    have hrow : ∀ w ∈ a.erase u, G.Adj y w := by
      apply (degreeIn_eq_card_iff y (a.erase u)).mp
      have he := degreeIn_erase_add G y u hu
      rw [if_neg hyu, hy3] at he
      rw [card_erase_of_mem hu, hcl.card_eq]
      omega
    refine ⟨u, hu, (degreeIn_eq_card_iff x a).mp (hx.trans hcl.card_eq.symm) u hu,
      (degreeIn_eq_card_iff r a).mp (hr.trans hcl.card_eq.symm) u hu,
      hcl.insert_erase ?_ hu⟩
    intro w hw
    apply hrow w
    simpa only [mem_sdiff, mem_erase, mem_singleton, and_comm] using hw

end Erdos577
