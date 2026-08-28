import ErdosProblems.Erdos577.FullLeafEqualityLabels

/-! Each first matching endpoint has inside degree five, and each second endpoint has seven. -/

namespace Erdos577.FullLeafCore

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {c : TriangleChain G} {p : Paw G} {s a : Finset V} {y : V}

lemma Configuration.second_first_degree_eq_triple (h : Configuration c p s a y) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    {v : V} (hv : v ∈ insert (p.vertices 3) a) :
    degreeIn G v (insert p.leaf s) = degreeIn G v (s.erase y) := by
  obtain ⟨hX, hY⟩ := h.marked_degrees_zero hcard hn
  have hnx : ¬G.Adj v p.leaf := fun hh ↦
    (degreeIn_eq_zero_iff p.leaf (insert (p.vertices 3) a)).mp hX v hv hh.symm
  have hny : ¬G.Adj v y := fun hh ↦
    (degreeIn_eq_zero_iff y (insert (p.vertices 3) a)).mp hY v hv hh.symm
  have he := degreeIn_erase_add G v y h.exposed
  rw [if_neg hny, add_zero] at he
  rw [degreeIn_insert G v p.leaf h.leaf_out, if_neg hnx, zero_add, ← he]

theorem Maximal.first_matched_inside_degree (hm : Maximal c p s a y) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ v, 2 * k ≤ G.degree v) (hn : ¬HasPacking G k)
    {v : V} (hv : v ∈ s.erase y) : degreeIn G v (p.support ∪ s ∪ a) = 5 := by
  have hvFirst : v ∈ insert p.leaf s := mem_insert_of_mem (mem_erase.mp hv).2
  have hrow := hm.first_matching_degree hcard hdeg hn hv
  have hmono := degreeIn_mono G v hm.1.second_five_subset
  have hbound := hm.1.first_core_degree hcard hn hvFirst
  have hcore : degreeIn G v (p.triangle ∪ a) = 1 := by omega
  rw [total_eq, degreeIn_union G v hm.1.five_disjoint_core,
    degreeIn_clique G hm.1.first_five_clique.isClique hvFirst,
    hm.1.first_five_clique.card_eq, hcore]

theorem Maximal.second_matched_inside_degree (hm : Maximal c p s a y) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ v, 2 * k ≤ G.degree v) (hn : ¬HasPacking G k)
    {v : V} (hv : v ∈ FullLeafEquality.matchedSecond p s a y) :
    degreeIn G v (p.support ∪ s ∪ a) = 7 := by
  obtain ⟨hvSecond, hpos⟩ := mem_filter.mp hv
  have hbound := (hm.1.matching_degrees hcard hn).2 v hvSecond
  have hrow : degreeIn G v (s.erase y) = 1 := by omega
  have hcore := hm.equality_core_complete hcard hdeg hn
  rw [total_eq, degreeIn_union G v hm.1.five_disjoint_core,
    hm.1.second_first_degree_eq_triple hcard hn hvSecond, hrow,
    degreeIn_clique G hcore.isClique (hm.1.second_five_subset hvSecond), hcore.card_eq]

theorem Maximal.matched_six_inside_contacts (hm : Maximal c p s a y) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ v, 2 * k ≤ G.degree v) (hn : ¬HasPacking G k) :
    contacts G ((s.erase y) ∪ FullLeafEquality.matchedSecond p s a y) (p.support ∪ s ∪ a) = 36 := by
  have hfirst : contacts G (s.erase y) (p.support ∪ s ∪ a) = 15 := by
    calc
      contacts G (s.erase y) (p.support ∪ s ∪ a) = ∑ _ ∈ s.erase y, (5 : ℕ) :=
        sum_congr rfl (fun _ hv ↦ hm.first_matched_inside_degree hcard hdeg hn hv)
      _ = 15 := by rw [sum_const, smul_eq_mul, hm.1.first_triple_clique.card_eq]
  have hsecond : contacts G (FullLeafEquality.matchedSecond p s a y) (p.support ∪ s ∪ a) = 21 := by
    calc
      contacts G (FullLeafEquality.matchedSecond p s a y) (p.support ∪ s ∪ a) =
          ∑ _ ∈ FullLeafEquality.matchedSecond p s a y, (7 : ℕ) :=
        sum_congr rfl (fun _ hv ↦ hm.second_matched_inside_degree hcard hdeg hn hv)
      _ = 21 := by
        rw [sum_const, smul_eq_mul, (hm.matched_second_triangle hcard hdeg hn).card_eq]
  have hd : Disjoint (s.erase y) (FullLeafEquality.matchedSecond p s a y) :=
    hm.1.triple_second_disjoint.mono_right (filter_subset _ _)
  rw [contacts_union_left G hd, hfirst, hsecond]

end Erdos577.FullLeafCore
