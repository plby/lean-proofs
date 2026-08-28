import ErdosProblems.Erdos577.FullLeafSixPawChain

/-! A positive first row cannot have nine contacts together with the second triangle. -/

namespace Erdos577.FullLeafSix

open Finset

lemma another_row_of_three {V : Type*} [DecidableEq V] {t : Finset V} {f : V → ℕ}
    (ht : t.card = 3) {u : V} (hu : u ∈ t) (huone : f u = 1)
    (hsum : 4 ≤ ∑ v ∈ t, f v) : ∃ v ∈ t.erase u, 2 ≤ f v := by
  by_contra hh
  push Not at hh
  have hbound : (∑ v ∈ t.erase u, f v) ≤ 2 := by
    calc
      (∑ v ∈ t.erase u, f v) ≤ ∑ _ ∈ t.erase u, (1 : ℕ) :=
        sum_le_sum (fun v hv ↦ by have := hh v hv; omega)
      _ = 2 := by rw [sum_const, smul_eq_mul, card_erase_of_mem hu, ht]
  have hsplit := sum_erase_add (s := t) f hu
  omega

end Erdos577.FullLeafSix

namespace Erdos577.FullLeafCore

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {c : TriangleChain G} {p : Paw G} {s a : Finset V} {y : V}

theorem Maximal.positive_first_paw_le_eight (hm : Maximal c p s a y) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ v, 2 * k ≤ G.degree v) (hn : ¬HasPacking G k)
    {j : Finset V} (hj : j ∈ c.blocks) (hjs : j ≠ s) (hja : j ≠ a)
    (htotal : 12 ≤ contacts G ((s.erase y) ∪ FullLeafEquality.matchedSecond p s a y) j)
    {u : V} (hu : u ∈ s.erase y) (hpos : 0 < degreeIn G u j) :
    contacts G (FullLeafEquality.matchedSecond p s a y) j + degreeIn G u j ≤ 8 := by
  by_contra hh
  obtain ⟨e, q, he, hq, hqu, hqt, _, _, _, _, _, _, hkeep⟩ :=
    hm.matched_paw_chain hcard hdeg hn hu
  obtain ⟨v, hv⟩ := c.property.blocks_quad j hj
  have hnine : 9 ≤ contacts G q.support v.support := by
    rw [q.contacts_support, hqu, hqt, hv]
    omega
  obtain ⟨hrow, hsum, houtside, _⟩ := he.toFeasible.first_paw_final hcard hdeg hn q hq
    (hkeep j hj hjs hja) v hv hnine (by rwa [hqu, hv])
  rw [hqu, hv] at hrow
  rw [q.contacts_support, hqu, hqt, hv] at hsum
  have htEight : contacts G (FullLeafEquality.matchedSecond p s a y) j = 8 := by omega
  rw [contacts_union_left G hm.1.matched_triples_disjoint, htEight] at htotal
  obtain ⟨w, hw, hwrow⟩ := FullLeafSix.another_row_of_three
    hm.1.first_triple_clique.card_eq hu hrow (show 4 ≤ contacts G (s.erase y) j by omega)
  have hwTriple := (mem_erase.mp hw).2
  have hwFirst : w ∈ insert p.leaf s := mem_insert_of_mem (mem_erase.mp hwTriple).2
  have hsupport : q.support = insert u (FullLeafEquality.matchedSecond p s a y) := by
    rw [q.support_eq, hqu, hqt]
  have hwout : w ∉ q.support ∪ v.support := by
    rw [hsupport, hv]
    intro hwbad
    rcases mem_union.mp hwbad with hwbad | hwbad
    · rcases mem_insert.mp hwbad with heq | hwbad
      · exact (mem_erase.mp hw).1 heq
      · exact disjoint_left.mp hm.1.matched_triples_disjoint hwTriple hwbad
    · exact disjoint_left.mp (hm.1.five_disjoint_block hj hjs) hwFirst hwbad
  have hf := houtside w hwout (by rwa [hv])
  rw [hqt, hv] at hf
  exact hm.1.first_no_factor hcard hn hwFirst hj hjs hja
    hm.1.matched_second_subset (hm.matched_second_triangle hcard hdeg hn).card_eq hf

theorem Maximal.second_nine_first_zero (hm : Maximal c p s a y) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ v, 2 * k ≤ G.degree v) (hn : ¬HasPacking G k)
    {j : Finset V} (hj : j ∈ c.blocks) (hjs : j ≠ s) (hja : j ≠ a)
    (htotal : 12 ≤ contacts G ((s.erase y) ∪ FullLeafEquality.matchedSecond p s a y) j)
    (hsecond : 9 ≤ contacts G (FullLeafEquality.matchedSecond p s a y) j) :
    contacts G (s.erase y) j = 0 := by
  apply sum_eq_zero
  intro u hu
  by_contra hne
  have hpos : 0 < degreeIn G u j := by omega
  have hbound := hm.positive_first_paw_le_eight hcard hdeg hn hj hjs hja htotal hu hpos
  omega

end Erdos577.FullLeafCore
