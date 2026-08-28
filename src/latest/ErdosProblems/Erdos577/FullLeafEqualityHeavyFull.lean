import ErdosProblems.Erdos577.FullLeafEqualitySaturation

/-! Every heavy block attains its budget, so its nonsparse five-by-four matrix is full. -/

namespace Erdos577.FullLeafCore

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {c : TriangleChain G} {p : Paw G} {s a : Finset V} {y : V}

theorem Maximal.every_further_budget_eq (hm : Maximal c p s a y) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ v, 2 * k ≤ G.degree v) (hn : ¬HasPacking G k)
    {j : Finset V} (hj : j ∈ FullLeafEquality.further c s a) :
    contacts G ((insert p.leaf s) ∪ insert (p.vertices 3) a) j = 20 +
      if 21 ≤ contacts G ((insert p.leaf s) ∪ insert (p.vertices 3) a) j then
        (FullLeafEquality.attachedVertices p s a y j).card else 0 := by
  apply FullLeafEquality.pointwise_eq_of_sum_eq
    (fun l hl ↦ hm.1.block_contact_budget hcard hdeg hn hl) ?_ hj
  have he := (hm.ten_row_equalities hcard hdeg hn).2.2
  rw [sum_add_distrib, sum_const, smul_eq_mul]
  rw [hm.covered_card hcard hn, FullLeafEquality.heavy, sum_filter] at he
  simpa only [Nat.mul_comm 20] using he

theorem Maximal.heavy_budget_eq (hm : Maximal c p s a y) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ v, 2 * k ≤ G.degree v) (hn : ¬HasPacking G k)
    {j : Finset V} (hj : j ∈ FullLeafEquality.heavy c p s a) :
    contacts G ((insert p.leaf s) ∪ insert (p.vertices 3) a) j =
      20 + (FullLeafEquality.attachedVertices p s a y j).card := by
  obtain ⟨hmem, hheavy⟩ := mem_filter.mp hj
  simpa only [if_pos hheavy] using hm.every_further_budget_eq hcard hdeg hn hmem

theorem Maximal.type40_second_contacts_twenty (hm : Maximal c p s a y) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ v, 2 * k ≤ G.degree v) (hn : ¬HasPacking G k)
    {j : Finset V} (hj : j ∈ FullLeafEquality.heavy c p s a)
    (htype : FullLeafHeavy.Type40 G p s y j) :
    contacts G (insert (p.vertices 3) a) j = 20 := by
  have he := hm.heavy_budget_eq hcard hdeg hn hj
  obtain ⟨⟨hj, _, _⟩, hheavy⟩ := FullLeafEquality.mem_heavy.mp hj
  rw [hm.1.type40_contact_split hj hheavy htype] at he
  omega

theorem Maximal.type41_first_contacts_twenty (hm : Maximal c p s a y) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ v, 2 * k ≤ G.degree v) (hn : ¬HasPacking G k)
    {j : Finset V} (hj : j ∈ FullLeafEquality.heavy c p s a)
    (htype : FullLeafHeavy.Type41 G p a j) : contacts G (insert p.leaf s) j = 20 := by
  have he := hm.heavy_budget_eq hcard hdeg hn hj
  obtain ⟨⟨hj, _, _⟩, hheavy⟩ := FullLeafEquality.mem_heavy.mp hj
  rw [hm.1.type41_contact_split hj hheavy htype] at he
  omega

theorem Maximal.type41_full_first_matrix (hm : Maximal c p s a y) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ v, 2 * k ≤ G.degree v) (hn : ¬HasPacking G k)
    {j : Finset V} (hj : j ∈ FullLeafEquality.heavy c p s a)
    (htype : FullLeafHeavy.Type41 G p a j) :
    ∀ x ∈ insert p.leaf s, ∀ d ∈ j, G.Adj x d := by
  have he := hm.type41_first_contacts_twenty hcard hdeg hn hj htype
  have hj4 := (c.property.blocks_quad j (FullLeafEquality.mem_heavy.mp hj).1.1).card
  have hmax : contacts G (insert p.leaf s) j = (insert p.leaf s).card * j.card := by
    rw [he, hm.1.first_five_clique.card_eq, hj4]
  intro x hx d hd
  exact (degreeIn_eq_card_iff x j).mp (FullLeafEquality.full_row_of_max_contacts hmax hx) d hd

end Erdos577.FullLeafCore
