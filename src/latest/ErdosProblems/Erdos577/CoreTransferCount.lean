import ErdosProblems.Erdos577.CoreTransferRoutes
import ErdosProblems.Erdos577.OutsideSelectedCount

/-! Exact six-row counts and both outside-block averages for the seven-vertex core argument. -/

namespace Erdos577.CoreTransfer

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

def rows (c : TriangleChain G) (q : Quadrilateral G) : Finset V :=
  c.remainder ∪ {q 1, q 3}

omit [DecidableRel G.Adj] in
lemma remainder_disjoint_lows (c : TriangleChain G) (q : Quadrilateral G)
    (hq : q.support ∈ c.blocks) : Disjoint c.remainder {q 1, q 3} := by
  apply disjoint_left.mpr
  intro u hu hlu
  have hqu : u ∈ q.support := by
    rcases mem_insert.mp hlu with rfl | hlu
    · exact (q.mem_support _).mpr ⟨1, rfl⟩
    · rw [mem_singleton] at hlu
      exact hlu ▸ (q.mem_support _).mpr ⟨3, rfl⟩
  exact (mem_sdiff.mp (c.complementPartition.block_subset hq hqu)).2 hu

omit [DecidableRel G.Adj] in
lemma rows_card (c : TriangleChain G) (q : Quadrilateral G) (hq : q.support ∈ c.blocks) :
    (rows c q).card = 6 := by
  have hne : q 1 ≠ q 3 := q.injective.ne (by decide : (1 : Fin 4) ≠ 3)
  rw [rows, card_union_of_disjoint (remainder_disjoint_lows c q hq), c.card_remainder,
    card_pair hne]

lemma rows_contacts (c : TriangleChain G) (q : Quadrilateral G) (hq : q.support ∈ c.blocks)
    (a : Finset V) : contacts G (rows c q) a = contacts G c.remainder a +
      degreeIn G (q 1) a + degreeIn G (q 3) a := by
  have hne : q 1 ≠ q 3 := q.injective.ne (by decide : (1 : Fin 4) ≠ 3)
  have hn : q 1 ∉ ({q 3} : Finset V) := by simpa only [mem_singleton] using hne
  have he : contacts G {q 1, q 3} a = degreeIn G (q 1) a + degreeIn G (q 3) a := by
    rw [contacts, sum_insert hn, sum_singleton]
  rw [rows, contacts_union_left G (remainder_disjoint_lows c q hq), he]
  omega

lemma remainder_contacts (c : TriangleChain G) (a : Finset V) :
    contacts G c.remainder a = degreeIn G c.terminal a + contacts G c.triangle a := by
  change contacts G (insert c.terminal c.triangle) a = _
  rw [contacts, sum_insert c.property.terminal_not_mem]
  rfl

theorem exists_heavy (c : TriangleChain G) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u)
    (bs : Finset (Finset V)) (hbs : bs ⊆ c.blocks) (s : Finset V) (hs : s.card = 6)
    (hinside : contacts G s (c.remainder ∪ bs.biUnion id) + 2 ≤ 12 * (bs.card + 1)) :
    ∃ a ∈ c.blocks, a ∉ bs ∧ 13 ≤ contacts G s a := by
  have hblocks := c.card_vertices
  have hsub := card_sdiff_of_subset hbs
  have hge := card_le_card hbs
  obtain ⟨a, ha, hna, hh⟩ := c.exists_heavy_outside_selected bs hbs s (2 * k) 12 hdeg (by
    rw [hs]
    omega)
  exact ⟨a, ha, hna, Nat.succ_le_of_lt hh⟩

theorem exists_two_heavy (c : TriangleChain G) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u)
    (bs : Finset (Finset V)) (hbs : bs ⊆ c.blocks) (s : Finset V) (hs : s.card = 6)
    (hinside : contacts G s (c.remainder ∪ bs.biUnion id) + 2 ≤ 12 * (bs.card + 1))
    (hexact : ∀ a ∈ c.blocks, a ∉ bs → 13 ≤ contacts G s a → contacts G s a ≤ 13) :
    ∃ a ∈ c.blocks, a ∉ bs ∧ 13 ≤ contacts G s a ∧
      ∃ b ∈ c.blocks, b ∉ bs ∧ b ≠ a ∧ 13 ≤ contacts G s b := by
  obtain ⟨a, ha, hna, hheavy⟩ := exists_heavy c hcard hdeg bs hbs s hs hinside
  have hupper := hexact a ha hna hheavy
  let ts := c.blocks \ bs
  have ham : a ∈ ts := mem_sdiff.mpr ⟨ha, hna⟩
  have hsum := sum_erase_add ts (fun b ↦ contacts G s b) ham
  have hsize := card_erase_of_mem ham
  have hpos : 0 < ts.card := card_pos.mpr ⟨a, ham⟩
  have hblocks := c.card_vertices
  have hsub : ts.card = c.blocks.card - bs.card := card_sdiff_of_subset hbs
  have hge := card_le_card hbs
  have htotal := minimum_degree_sum G s (2 * k) (fun u _ ↦ hdeg u)
  rw [hs] at htotal
  have hid := c.contacts_selected_core_add_outside bs hbs s
  change contacts G s (c.remainder ∪ bs.biUnion id) + ∑ b ∈ ts, contacts G s b =
    contacts G s univ at hid
  obtain ⟨b, hb, hh⟩ := exists_heavy_block G s (ts.erase a) id 12 (by
    simp only [id_eq]
    omega)
  obtain ⟨hba, hbt⟩ := mem_erase.mp hb
  obtain ⟨hbc, hnb⟩ := mem_sdiff.mp hbt
  exact ⟨a, ha, hna, hheavy, b, hbc, hnb, hba, Nat.succ_le_of_lt hh⟩

end Erdos577.CoreTransfer
