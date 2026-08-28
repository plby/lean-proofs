import ErdosProblems.Erdos577.FullLeafEqualityCoverage

/-! Each heavy block contributes at most twenty contacts plus its actual sparse vertices. -/

namespace Erdos577.FullLeafCore

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {c : TriangleChain G} {p : Paw G} {s a : Finset V} {y : V}
variable (h : Configuration c p s a y)

include h

lemma Configuration.attached_vertices_type40 {j : Finset V} (hj : j ∈ c.blocks)
    (hheavy : 21 ≤ contacts G ((insert p.leaf s) ∪ insert (p.vertices 3) a) j)
    (htype : FullLeafHeavy.Type40 G p s y j) :
    FullLeafEquality.attachedVertices p s a y j =
      (s.erase y).filter (fun v ↦ 0 < degreeIn G v j) := by
  ext v
  rw [FullLeafEquality.mem_attachedVertices, mem_filter]
  constructor
  · rintro ⟨hside, hrow⟩
    rcases hside with ⟨hv, _⟩ | ⟨_, h41⟩
    · exact ⟨hv, by omega⟩
    · exact False.elim (h.heavy_types_disjoint hj hheavy ⟨htype, h41⟩)
  · rintro ⟨hv, hpos⟩
    have hb := htype.2.2.1 v hv
    exact ⟨Or.inl ⟨hv, htype⟩, by omega⟩

lemma Configuration.attached_vertices_type41 {j : Finset V} (hj : j ∈ c.blocks)
    (hheavy : 21 ≤ contacts G ((insert p.leaf s) ∪ insert (p.vertices 3) a) j)
    (htype : FullLeafHeavy.Type41 G p a j) :
    FullLeafEquality.attachedVertices p s a y j =
      (insert (p.vertices 3) a).filter (fun v ↦ 0 < degreeIn G v j) := by
  ext v
  rw [FullLeafEquality.mem_attachedVertices, mem_filter]
  constructor
  · rintro ⟨hside, hrow⟩
    rcases hside with ⟨_, h40⟩ | ⟨hv, _⟩
    · exact False.elim (h.heavy_types_disjoint hj hheavy ⟨h40, htype⟩)
    · exact ⟨hv, by omega⟩
  · rintro ⟨hv, hpos⟩
    have hb := htype.1 v hv
    exact ⟨Or.inr ⟨hv, htype⟩, by omega⟩

lemma Configuration.type40_contact_split {j : Finset V} (hj : j ∈ c.blocks)
    (hheavy : 21 ≤ contacts G ((insert p.leaf s) ∪ insert (p.vertices 3) a) j)
    (htype : FullLeafHeavy.Type40 G p s y j) :
    contacts G ((insert p.leaf s) ∪ insert (p.vertices 3) a) j =
      contacts G (insert (p.vertices 3) a) j +
        (FullLeafEquality.attachedVertices p s a y j).card := by
  have he := FullLeafSparse.contacts_eq_positive_rows htype.2.2.1
  rw [← h.attached_vertices_type40 hj hheavy htype] at he
  rw [h.combined_contacts, h.first_contacts, htype.1, htype.2.1, zero_add, zero_add, he, add_comm]

lemma Configuration.type41_contact_split {j : Finset V} (hj : j ∈ c.blocks)
    (hheavy : 21 ≤ contacts G ((insert p.leaf s) ∪ insert (p.vertices 3) a) j)
    (htype : FullLeafHeavy.Type41 G p a j) :
    contacts G ((insert p.leaf s) ∪ insert (p.vertices 3) a) j =
      contacts G (insert p.leaf s) j + (FullLeafEquality.attachedVertices p s a y j).card := by
  have he := FullLeafSparse.contacts_eq_positive_rows htype.1
  rw [← h.attached_vertices_type41 hj hheavy htype] at he
  rw [h.combined_contacts, he]

theorem Configuration.heavy_contact_budget {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ v, 2 * k ≤ G.degree v) (hn : ¬HasPacking G k)
    {j : Finset V} (hj : j ∈ c.blocks) (hjs : j ≠ s) (hja : j ≠ a)
    (hheavy : 21 ≤ contacts G ((insert p.leaf s) ∪ insert (p.vertices 3) a) j) :
    contacts G ((insert p.leaf s) ∪ insert (p.vertices 3) a) j ≤
      20 + (FullLeafEquality.attachedVertices p s a y j).card := by
  rcases h.heavy_types hcard hdeg hn hj hjs hja hheavy with h40 | h41
  · rw [h.type40_contact_split hj hheavy h40]
    have hb := contacts_le_card_mul G (insert (p.vertices 3) a) j
    rw [h.second_five_card, (c.property.blocks_quad j hj).card] at hb
    omega
  · rw [h.type41_contact_split hj hheavy h41]
    have hb := contacts_le_card_mul G (insert p.leaf s) j
    rw [h.first_five_clique.card_eq, (c.property.blocks_quad j hj).card] at hb
    omega

theorem Configuration.block_contact_budget {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ v, 2 * k ≤ G.degree v) (hn : ¬HasPacking G k)
    {j : Finset V} (hj : j ∈ FullLeafEquality.further c s a) :
    contacts G ((insert p.leaf s) ∪ insert (p.vertices 3) a) j ≤ 20 +
      if 21 ≤ contacts G ((insert p.leaf s) ∪ insert (p.vertices 3) a) j then
        (FullLeafEquality.attachedVertices p s a y j).card else 0 := by
  obtain ⟨hj, hjs, hja⟩ := FullLeafEquality.mem_further.mp hj
  split_ifs with hheavy
  · exact h.heavy_contact_budget hcard hdeg hn hj hjs hja hheavy
  · omega

omit h in
theorem Maximal.outside_contact_budget (hm : Maximal c p s a y) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ v, 2 * k ≤ G.degree v) (hn : ¬HasPacking G k) :
    (∑ j ∈ FullLeafEquality.further c s a,
      contacts G ((insert p.leaf s) ∪ insert (p.vertices 3) a) j) ≤
      20 * (FullLeafEquality.further c s a).card + (FullLeafEquality.covered c p s a y).card := by
  have hb := sum_le_sum (fun j hj ↦ hm.1.block_contact_budget hcard hdeg hn hj)
  rw [sum_add_distrib, sum_const, smul_eq_mul] at hb
  rw [hm.covered_card hcard hn, FullLeafEquality.heavy, sum_filter, Nat.mul_comm 20]
  exact hb

end Erdos577.FullLeafCore
