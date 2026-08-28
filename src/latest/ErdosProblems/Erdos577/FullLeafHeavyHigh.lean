import ErdosProblems.Erdos577.FullLeafHeavyCounts

/-! A high first-five row forces a complete block and at least nine first-triple contacts. -/

namespace Erdos577.FullLeafCore

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {c : TriangleChain G} {p : Paw G} {s a : Finset V} {y : V}

theorem Configuration.high_first_preparation (h : Configuration c p s a y) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    {j : Finset V} (hj : j ∈ c.blocks) (hjs : j ≠ s) (hja : j ≠ a)
    (hheavy : 21 ≤ contacts G ((insert p.leaf s) ∪ insert (p.vertices 3) a) j)
    {x : V} (hx : x ∈ insert p.leaf s) (hrow : 3 ≤ degreeIn G x j) :
    (∀ v ∈ j, degreeIn G v (p.triangle ∪ a) ≤ 1) ∧
      contacts G (insert (p.vertices 3) a) j ≤ 4 ∧
      17 ≤ contacts G (insert p.leaf s) j ∧ G.IsNClique 4 j ∧
      9 ≤ contacts G (s.erase y) j := by
  have hcolumns (v : V) (hv : v ∈ j) : degreeIn G v (p.triangle ∪ a) ≤ 1 :=
    h.core_degree_of_first_replacement hcard hn hx hj hjs hja hv
      (h.first_universal_replacements hx hj hjs hrow v hv)
  have hj4 := (c.property.blocks_quad j hj).card
  have hsecond : contacts G (insert (p.vertices 3) a) j ≤ 4 := by
    rw [contacts_comm]
    calc
      contacts G j (insert (p.vertices 3) a) ≤ ∑ _ ∈ j, (1 : ℕ) :=
        sum_le_sum fun v hv ↦ (degreeIn_mono G v h.second_five_subset).trans (hcolumns v hv)
      _ = 4 := by simp only [sum_const, smul_eq_mul, mul_one, hj4]
  rw [h.combined_contacts] at hheavy
  have hfirst : 17 ≤ contacts G (insert p.leaf s) j := by omega
  have hfull : ∃ z ∈ insert p.leaf s, degreeIn G z j = 4 := by
    by_contra! hh
    have hbound (z : V) (hz : z ∈ insert p.leaf s) : degreeIn G z j ≤ 3 := by
      have hb := degreeIn_le_card G z j
      have hn4 := hh z hz
      omega
    have hsum : contacts G (insert p.leaf s) j ≤ 15 := by
      calc
        contacts G (insert p.leaf s) j ≤ ∑ _ ∈ insert p.leaf s, (3 : ℕ) := sum_le_sum hbound
        _ = 15 := by simp only [sum_const, smul_eq_mul, h.first_five_clique.card_eq]
    omega
  obtain ⟨z, hz, hz4⟩ := hfull
  have hcl := h.complete_of_first_full hz hj hjs hz4
  have hx4 := degreeIn_le_card G p.leaf j
  have hy4 := degreeIn_le_card G y j
  have he := h.first_contacts j
  exact ⟨hcolumns, hsecond, hfirst, hcl, by omega⟩

end Erdos577.FullLeafCore
