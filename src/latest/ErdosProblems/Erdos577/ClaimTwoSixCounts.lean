import ErdosProblems.Erdos577.FullLeafSixRows

/-! Every further block attains the six-row upper bound twelve. -/

namespace Erdos577.FullLeafCore

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {c : TriangleChain G} {p : Paw G} {s a : Finset V} {y : V}

lemma Configuration.core_further_split (h : Configuration c p s a y) (rows : Finset V) :
    contacts G rows (p.support ∪ s ∪ a) +
      ∑ j ∈ FullLeafEquality.further c s a, contacts G rows j = contacts G rows univ := by
  have hsub : ({s, a} : Finset (Finset V)) ⊆ c.blocks :=
    insert_subset h.first (singleton_subset_iff.mpr h.core)
  have he := c.contacts_selected_core_add_outside {s, a} hsub rows
  simpa only [biUnion_insert, singleton_biUnion, id_eq, ← h.paw, ← union_assoc,
    FullLeafEquality.further] using he

theorem Maximal.further_six_le_twelve (hm : Maximal c p s a y) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ v, 2 * k ≤ G.degree v) (hn : ¬HasPacking G k)
    {j : Finset V} (hj : j ∈ FullLeafEquality.further c s a) :
    contacts G ((s.erase y) ∪ FullLeafEquality.matchedSecond p s a y) j ≤ 12 := by
  obtain ⟨hj, hjs, hja⟩ := FullLeafEquality.mem_further.mp hj
  by_cases hlow : contacts G ((s.erase y) ∪ FullLeafEquality.matchedSecond p s a y) j < 12
  · omega
  · have htwelve : 12 ≤ contacts G ((s.erase y) ∪ FullLeafEquality.matchedSecond p s a y) j :=
      by omega
    have hfirst := contacts_le_card_mul G (s.erase y) j
    have hsecond := contacts_le_card_mul G (FullLeafEquality.matchedSecond p s a y) j
    rw [hm.1.first_triple_clique.card_eq, (c.property.blocks_quad j hj).card] at hfirst
    rw [(hm.matched_second_triangle hcard hdeg hn).card_eq,
      (c.property.blocks_quad j hj).card] at hsecond
    rcases hm.six_row_alternative hcard hdeg hn hj hjs hja htwelve with hz | hz | ⟨ht, hr⟩
    · rw [contacts_union_left G hm.1.matched_triples_disjoint, hz, zero_add]
      exact hsecond
    · rw [contacts_union_left G hm.1.matched_triples_disjoint, hz, add_zero]
      exact hfirst
    · have he : contacts G (s.erase y) j = 6 := by
        calc
          contacts G (s.erase y) j = ∑ _ ∈ s.erase y, (2 : ℕ) := sum_congr rfl hr
          _ = 6 := by rw [sum_const, smul_eq_mul, hm.1.first_triple_clique.card_eq]
      rw [contacts_union_left G hm.1.matched_triples_disjoint, he, ht]

theorem Maximal.further_six_eq_twelve (hm : Maximal c p s a y) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ v, 2 * k ≤ G.degree v) (hn : ¬HasPacking G k)
    {j : Finset V} (hj : j ∈ FullLeafEquality.further c s a) :
    contacts G ((s.erase y) ∪ FullLeafEquality.matchedSecond p s a y) j = 12 := by
  have hcount : ((s.erase y) ∪ FullLeafEquality.matchedSecond p s a y).card = 6 := by
    rw [card_union_of_disjoint hm.1.matched_triples_disjoint, hm.1.first_triple_clique.card_eq,
      (hm.matched_second_triangle hcard hdeg hn).card_eq]
  have hdegree := minimum_degree_sum G ((s.erase y) ∪ FullLeafEquality.matchedSecond p s a y)
    (2 * k) (fun v _ ↦ hdeg v)
  rw [hcount] at hdegree
  have hsplit := hm.1.core_further_split ((s.erase y) ∪ FullLeafEquality.matchedSecond p s a y)
  rw [hm.matched_six_inside_contacts hcard hdeg hn] at hsplit
  have hf := hm.1.further_card hcard
  have hk := hm.1.three_le_parameter hcard
  have hupper := sum_le_sum (fun b hb ↦ hm.further_six_le_twelve hcard hdeg hn hb)
  have htotal : (∑ b ∈ FullLeafEquality.further c s a,
      contacts G ((s.erase y) ∪ FullLeafEquality.matchedSecond p s a y) b) =
      ∑ _ ∈ FullLeafEquality.further c s a, (12 : ℕ) := by
    rw [sum_const, smul_eq_mul] at hupper ⊢
    omega
  exact FullLeafEquality.pointwise_eq_of_sum_eq
    (fun b hb ↦ hm.further_six_le_twelve hcard hdeg hn hb) htotal hj

end Erdos577.FullLeafCore
