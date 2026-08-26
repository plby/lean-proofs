import ErdosProblems.Erdos556.TwoThreeCycle

/-! An odd monochromatic cycle forces a monochromatic cycle one vertex shorter. -/

namespace Erdos556

open SimpleGraph

theorem monochromatic_predecessor_of_odd_cycle {V : Type*} (G : SimpleGraph V)
    (m : ℕ) (hm : 7 ≤ m) (hodd : Odd m) (hc : cycleGraph m ⊑ G) :
    cycleGraph (m - 1) ⊑ G ∨ cycleGraph (m - 1) ⊑ Gᶜ := by
  classical
  by_contra hn
  have hno : (¬ cycleGraph (m - 1) ⊑ G) ∧ (¬ cycleGraph (m - 1) ⊑ Gᶜ) := not_or.mp hn
  obtain ⟨r, hr⟩ := hodd
  have hmr : m = 2 * r + 1 := by omega
  subst m
  obtain ⟨f⟩ := hc
  have h2 := complement_short_chords_of_cycle_copy (by omega : 4 ≤ 2 * r + 1) f hno.1
  have h3 := three_chords_of_no_predecessor_cycles hm ⟨r, by omega⟩ f hno.1 hno.2
  obtain ⟨v, c, hcycle, hlen⟩ := exists_even_cycle_of_two_three_steps r (by omega) f f.injective h2 h3
  apply hno.2
  apply (cycleGraph_isContained_iff (by omega : 2 < 2 * r + 1 - 1)).mpr
  exact ⟨v, c, hcycle, by omega⟩

theorem exists_minimal_even_monochromatic_cycle {V : Type*} (G : SimpleGraph V)
    (n : ℕ) (hn : 7 ≤ n) (hno : ¬ cycleGraph n ⊑ G) (hnoc : ¬ cycleGraph n ⊑ Gᶜ)
    (hex : ∃ m, n ≤ m ∧ (cycleGraph m ⊑ G ∨ cycleGraph m ⊑ Gᶜ)) :
    ∃ m, n < m ∧ Even m ∧ (cycleGraph m ⊑ G ∨ cycleGraph m ⊑ Gᶜ) ∧
      ¬ cycleGraph (m - 1) ⊑ G ∧ ¬ cycleGraph (m - 1) ⊑ Gᶜ := by
  classical
  let m := Nat.find hex
  have hm := Nat.find_spec hex
  change n ≤ m ∧ (cycleGraph m ⊑ G ∨ cycleGraph m ⊑ Gᶜ) at hm
  have hlt : n < m := by
    have hne : m ≠ n := by
      intro h
      rcases hm.2 with hG | hGc
      · exact hno (h ▸ hG)
      · exact hnoc (h ▸ hGc)
    omega
  have hpred : ¬ (cycleGraph (m - 1) ⊑ G ∨ cycleGraph (m - 1) ⊑ Gᶜ) := by
    intro h
    apply Nat.find_min hex (show m - 1 < Nat.find hex by change m - 1 < m; omega)
    exact ⟨by omega, h⟩
  have heven : Even m := by
    rcases Nat.even_or_odd m with h | h
    · exact h
    · exfalso
      rcases hm.2 with hG | hGc
      · exact hpred (monochromatic_predecessor_of_odd_cycle G m (by omega) h hG)
      · rcases monochromatic_predecessor_of_odd_cycle Gᶜ m (by omega) h hGc with h₁ | h₂
        · exact hpred (Or.inr h₁)
        · exact hpred (Or.inl (by simpa only [compl_compl] using h₂))
  exact ⟨m, hlt, heven, hm.2, fun h => hpred (Or.inl h), fun h => hpred (Or.inr h)⟩

#print axioms monochromatic_predecessor_of_odd_cycle
#print axioms exists_minimal_even_monochromatic_cycle

end Erdos556
