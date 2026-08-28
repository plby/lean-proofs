import ErdosProblems.Erdos577.ClaimTwoSixCounts

/-! Each block has an even first row and exact weighted contribution twelve. -/

namespace Erdos577.FullLeafCore

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {c : TriangleChain G} {p : Paw G} {s a : Finset V} {y : V}

theorem Maximal.further_contribution_cases (hm : Maximal c p s a y) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ v, 2 * k ≤ G.degree v) (hn : ¬HasPacking G k)
    {u : V} (hu : u ∈ s.erase y) {j : Finset V} (hj : j ∈ FullLeafEquality.further c s a) :
    (degreeIn G u j = 0 ∧ contacts G (FullLeafEquality.matchedSecond p s a y) j = 12) ∨
      (degreeIn G u j = 4 ∧ contacts G (FullLeafEquality.matchedSecond p s a y) j = 0) ∨
      (degreeIn G u j = 2 ∧ contacts G (FullLeafEquality.matchedSecond p s a y) j = 6) := by
  have he := hm.further_six_eq_twelve hcard hdeg hn hj
  obtain ⟨hj, hjs, hja⟩ := FullLeafEquality.mem_further.mp hj
  have halt := hm.six_row_alternative hcard hdeg hn hj hjs hja he.ge
  rw [contacts_union_left G hm.1.matched_triples_disjoint] at he
  rcases halt with hz | hz | ⟨ht, hr⟩
  · have hle : degreeIn G u j ≤ contacts G (s.erase y) j :=
      single_le_sum (fun v _ ↦ Nat.zero_le (degreeIn G v j)) hu
    exact Or.inl ⟨by omega, by omega⟩
  · have hfirst : contacts G (s.erase y) j = (s.erase y).card * j.card := by
      rw [hm.1.first_triple_clique.card_eq, (c.property.blocks_quad j hj).card]
      omega
    have hrow := FullLeafEquality.full_row_of_max_contacts hfirst hu
    rw [(c.property.blocks_quad j hj).card] at hrow
    exact Or.inr (Or.inl ⟨hrow, hz⟩)
  · exact Or.inr (Or.inr ⟨hr u hu, ht⟩)

theorem Maximal.further_balance_and_even (hm : Maximal c p s a y) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ v, 2 * k ≤ G.degree v) (hn : ¬HasPacking G k)
    {u : V} (hu : u ∈ s.erase y) {j : Finset V} (hj : j ∈ FullLeafEquality.further c s a) :
    3 * degreeIn G u j + contacts G (FullLeafEquality.matchedSecond p s a y) j = 12 ∧
      degreeIn G u j = 2 * (degreeIn G u j / 2) := by
  rcases hm.further_contribution_cases hcard hdeg hn hu hj with ⟨hd, ht⟩ | ⟨hd, ht⟩ | ⟨hd, ht⟩ <;>
    rw [hd, ht] <;> decide

end Erdos577.FullLeafCore
